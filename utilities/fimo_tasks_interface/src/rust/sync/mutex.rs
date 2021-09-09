use crate::rust::sync::condvar::RawCondvar;
use crate::rust::sync::SpinWait;
use crate::rust::{NotifyFn, TaskHandle, WaitOnFn};
use std::cell::UnsafeCell;
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Deref, DerefMut};
use std::sync::atomic::{AtomicU8, Ordering};

/// A mutex.
pub struct Mutex<T: ?Sized> {
    raw: RawMutex,
    data: UnsafeCell<T>,
}

/// A mutex guard.
pub struct MutexGuard<'a, T: ?Sized> {
    pub(crate) lock: &'a Mutex<T>,
}

/// A raw mutex.
#[derive(Debug)]
pub struct RawMutex {
    state: AtomicU8,
    condvar: RawCondvar,
}

// Bit that is set when the mutex is locked.
const LOCKED_BIT: u8 = 0b01;

// Bit that is set when there are tasks waiting to acquire the mutex.
const WAITING_BIT: u8 = 0b10;

// State of an unlocked mutex with no waiters.
const INIT_STATE: u8 = 0;

impl<T> Mutex<T> {
    /// Constructs a new `Mutex<T>`.
    ///
    /// # Panics
    ///
    /// **Must** be run from within a task.
    pub fn new(val: T) -> Self {
        Self {
            raw: RawMutex::new(),
            data: UnsafeCell::new(val),
        }
    }
}

impl<T: ?Sized> Mutex<T> {
    /// Locks the Mutex, blocking the task until it can be acquired.
    ///
    /// # Panics
    ///
    /// **Must** be run from within a task.
    pub fn lock(&self) -> MutexGuard<'_, T> {
        self.raw.lock();
        MutexGuard { lock: self }
    }

    /// Tries to lock the Mutex without blocking the task.
    pub fn try_lock(&self) -> Option<MutexGuard<'_, T>> {
        if self.raw.try_lock() {
            Some(MutexGuard { lock: self })
        } else {
            None
        }
    }

    /// Force the unlock of the mutex.
    ///
    /// Can be used to unlock the mutex, in case the guard was
    /// forgotten.
    ///
    /// # Panics
    ///
    /// **Must** be run from within a task.
    ///
    /// # Safety
    ///
    /// This function must only be called if this task logically
    /// owns a lock, which was discarded using mem::forget.
    pub unsafe fn force_unlock(&self) {
        self.raw.unlock();
    }

    /// Returns a raw pointer to the underlying data.
    ///
    /// This is useful when combined with mem::forget to hold a
    /// lock without the need to maintain a MutexGuard object alive,
    /// for example when dealing with FFI.
    ///
    /// # Panics
    ///
    /// **Must** be run from within a task.
    ///
    /// # Safety
    ///
    /// You must ensure that no data races occur when dereferencing
    /// the pointer.  
    pub unsafe fn data_ptr(&self) -> *mut T {
        self.data.get()
    }

    /// Returns the raw mutex.
    pub fn get_raw(&self) -> &RawMutex {
        &self.raw
    }

    /// Consumes this mutex, returning the underlying data.
    pub fn into_inner(self) -> T
    where
        T: Sized,
    {
        self.data.into_inner()
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the `Mutex` mutably, no actual locking needs to
    /// take place - the mutable borrow statically guarantees no lock exists.
    pub fn get_mut(&mut self) -> &mut T {
        self.data.get_mut()
    }
}

// The implementation is inspired by the RawMutex of the parking_lot crate,
// which is licensed under the following license:
//
// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.
impl RawMutex {
    /// Constructs a new `RawMutex`.
    ///
    /// # Panics
    ///
    /// **Must** be run from within a task.
    #[inline]
    pub fn new() -> Self {
        Self {
            state: AtomicU8::new(INIT_STATE),
            condvar: RawCondvar::new(),
        }
    }

    /// Locks the mutex, blocking the task until the lock could be acquired.
    ///
    /// # Panics
    ///
    /// **Must** be run from within a task.
    #[inline]
    pub fn lock(&self) {
        if self
            .state
            .compare_exchange_weak(INIT_STATE, LOCKED_BIT, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            self.lock_slow()
        }
    }

    /// Tries to lock the mutex without blocking the task.
    ///
    /// # Panics
    ///
    /// **Must** be run from within a task.
    #[inline]
    pub fn try_lock(&self) -> bool {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            if state & LOCKED_BIT != 0 {
                return false;
            }
            match self.state.compare_exchange_weak(
                state,
                state | LOCKED_BIT,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(x) => {
                    state = x;
                }
            }
        }
    }

    /// Unlocks the mutex.
    ///
    /// # Panics
    ///
    /// **Must** be run from within a task.
    ///
    /// # Safety
    ///
    /// This function must only be called if this task owns the lock.
    #[inline]
    pub unsafe fn unlock(&self) {
        if self
            .state
            .compare_exchange(LOCKED_BIT, INIT_STATE, Ordering::Release, Ordering::Relaxed)
            .is_ok()
        {
            return;
        }
        self.unlock_slow(None);
    }

    #[inline]
    pub(crate) unsafe fn unlock_with_notify(
        &self,
        notify_fn: &mut dyn FnMut(TaskHandle, Option<NotifyFn>),
    ) {
        if self
            .state
            .compare_exchange(LOCKED_BIT, INIT_STATE, Ordering::Release, Ordering::Relaxed)
            .is_ok()
        {
            return;
        }
        self.unlock_slow(Some(notify_fn));
    }

    #[cold]
    fn lock_slow(&self) {
        let mut spinwait = SpinWait::new();
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            // Grab the lock if it isn't locked, even if there is a queue on it.
            if state & LOCKED_BIT == 0 {
                match self.state.compare_exchange_weak(
                    state,
                    state | LOCKED_BIT,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return,
                    Err(x) => state = x,
                }
            }

            // If there is no queue, try spinning a few times
            if state & WAITING_BIT == 0 && spinwait.spin() {
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            // Set the waiting bit.
            if state & WAITING_BIT == 0 {
                if let Err(x) = self.state.compare_exchange_weak(
                    state,
                    state | WAITING_BIT,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    state = x;
                    continue;
                }
            }

            // Put the task to sleep until it is woken up by an unlock.
            let data_ptr = self as *const _ as usize;
            let validate = |data: usize| {
                let raw = unsafe { &*(data as *const Self) };
                raw.state.load(Ordering::Relaxed) == LOCKED_BIT | WAITING_BIT
            };

            self.condvar.wait_on_if(Some(WaitOnFn {
                data: data_ptr,
                validate,
                after_sleep: |_, _| {},
            }));

            // Loop back and try locking again.
            spinwait.reset();
            state = self.state.load(Ordering::Relaxed);
        }
    }

    #[cold]
    unsafe fn unlock_slow(&self, notify_fn: Option<&mut dyn FnMut(TaskHandle, Option<NotifyFn>)>) {
        // Wake up one task and leave the waiting bit set if
        // there are waiting tasks.
        let data_ptr = self as *const _ as usize;
        let callback = |waiters: usize, data: usize| {
            let raw = &*(data as *const Self);

            // Clear the locked bit, and the waiting bit as well if there
            // are no more parked tasks.
            if waiters != 0 {
                raw.state.store(WAITING_BIT, Ordering::Release);
            } else {
                raw.state.store(INIT_STATE, Ordering::Release);
            }
        };

        let after_wake = Some(NotifyFn {
            data: data_ptr,
            function: callback,
        });

        if let Some(notify_fn) = notify_fn {
            self.condvar.notify_one_with_function(after_wake, notify_fn)
        } else {
            self.condvar.notify_one_and_then(after_wake)
        }
    }
}

impl<T: ?Sized + Debug> Debug for Mutex<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.try_lock() {
            Some(guard) => f.debug_struct("Mutex").field("data", &guard).finish(),
            None => {
                struct Placeholder;
                impl Debug for Placeholder {
                    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                        write!(f, "<locked>")
                    }
                }

                f.debug_struct("Mutex").field("data", &Placeholder).finish()
            }
        }
    }
}

impl<T: Default> Default for Mutex<T> {
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl<T> From<T> for Mutex<T> {
    fn from(val: T) -> Self {
        Self::new(val)
    }
}

unsafe impl<T: ?Sized + Send> Send for Mutex<T> {}

unsafe impl<T: ?Sized + Send> Sync for Mutex<T> {}

impl<T: ?Sized> Drop for MutexGuard<'_, T> {
    fn drop(&mut self) {
        // unlock and notify waiters.
        unsafe { self.lock.force_unlock() };
    }
}

impl<T: ?Sized> !Send for MutexGuard<'_, T> {}

unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T> {}

impl<T: ?Sized> Deref for MutexGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // we own the lock.
        unsafe { &*self.lock.data_ptr() }
    }
}

impl<T: ?Sized> DerefMut for MutexGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // we own the lock.
        unsafe { &mut *self.lock.data_ptr() }
    }
}

impl<T: ?Sized + Debug> Debug for MutexGuard<'_, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized + Display> Display for MutexGuard<'_, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&**self, f)
    }
}

impl Default for RawMutex {
    fn default() -> Self {
        Self::new()
    }
}
