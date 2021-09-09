use crate::rust::sync::{Mutex, MutexGuard};
use crate::rust::{get_runtime, NotifyFn, RawTask, TaskHandle, WaitOnFn};
use std::mem::{forget, ManuallyDrop};
use std::sync::atomic::{AtomicPtr, Ordering};

/// A Condition Variable.
#[derive(Debug)]
pub struct Condvar {
    raw: RawCondvar,
    state: AtomicPtr<Mutex<()>>,
}

#[derive(Debug)]
pub(crate) struct RawCondvar {
    raw: RawTask,
}

#[derive(Debug)]
pub(crate) struct CondvarWaitData<'a, 's, T> {
    unlocked: bool,
    bad_mutex: bool,
    state: &'s AtomicPtr<Mutex<()>>,
    guard: ManuallyDrop<MutexGuard<'a, T>>,
}

impl Default for Condvar {
    fn default() -> Self {
        Self::new()
    }
}

impl Condvar {
    /// Constructs a new `Condvar`.
    ///
    /// # Panics
    ///
    /// **Must** be run from within a task.
    pub fn new() -> Self {
        Self {
            raw: RawCondvar::new(),
            state: AtomicPtr::new(std::ptr::null_mut()),
        }
    }

    /// Blocks the current task until this condition variable receives a notification.
    ///
    /// # Panics
    ///
    /// **Must** be run from within a task.
    /// This function may panic if it is used with more than one mutex over time.
    pub fn wait<'a, T>(&self, guard: MutexGuard<'a, T>) -> MutexGuard<'a, T> {
        // save a reference to the mutex.
        let mutex = guard.lock;

        let mut data = CondvarWaitData {
            unlocked: false,
            bad_mutex: false,
            state: &self.state,
            guard: ManuallyDrop::new(guard),
        };

        // wait for a signal and unlock the mutex.
        self.raw.wait_and_release(&mut data);

        // panic if we tried to use multiple mutexes with a Condvar.
        if data.bad_mutex {
            unsafe { ManuallyDrop::drop(&mut data.guard) }
            panic!("attempted to use a condition variable with more than one mutex")
        }

        // if the mutex was unlocked, i.e. the task was put to sleep,
        // we need to lock the mutex. Otherwise we can simply read it.
        if data.unlocked {
            Mutex::lock(mutex)
        } else {
            unsafe { ManuallyDrop::take(&mut data.guard) }
        }
    }

    /// Notifies one waiting task.
    ///
    /// # Panics
    ///
    /// **Must** be run from within a task.
    pub fn notify_one(&self) {
        self.raw.notify_one_and_reset(&self.state)
    }

    /// Notifies all waiting tasks.
    ///
    /// # Panics
    ///
    /// **Must** be run from within a task.
    pub fn notify_all(&self) {
        self.raw.notify_all_and_reset(&self.state)
    }
}

impl RawCondvar {
    pub(crate) fn new() -> Self {
        Self {
            raw: get_runtime().spawn_empty_blocked(&[]),
        }
    }

    pub(crate) fn wait_on_if(&self, predicate: Option<WaitOnFn>) {
        self.raw.wait_on_if(predicate)
    }

    pub(crate) fn wait_and_release<'a, 's, T: 'a + 's>(
        &self,
        data: &mut CondvarWaitData<'a, 's, T>,
    ) {
        fn validate<'a, 's, T: 'a + 's>(data: usize) -> bool {
            let data = unsafe { &mut *(data as *mut CondvarWaitData<'a, 's, T>) };
            let lock_address = data.guard.lock as *const _ as *mut Mutex<()>;

            // ensure we don't use two different mutexes with the same
            // Condvar at the same time. We can use the relaxed ordering
            // as we are in the locked runtime.
            let state = data.state.load(Ordering::Relaxed);
            if state.is_null() {
                data.state.store(lock_address, Ordering::Relaxed);
            } else if state != lock_address {
                data.bad_mutex = true;
                return false;
            }

            true
        }

        fn unlock_mutex<'a, 's, T: 'a + 's>(
            notify_fn: &mut dyn FnMut(TaskHandle, Option<NotifyFn>),
            data: usize,
        ) {
            let data = unsafe { &mut *(data as *mut CondvarWaitData<'a, 's, T>) };
            let guard = unsafe { ManuallyDrop::take(&mut data.guard) };

            // unlock the mutex with `notify_fn`.
            data.unlocked = true;
            let raw = guard.lock.get_raw();
            unsafe { raw.unlock_with_notify(notify_fn) };
            forget(guard);
        }

        let data_ptr = data as *mut _ as usize;
        self.wait_on_if(Some(WaitOnFn {
            data: data_ptr,
            validate: validate::<T>,
            after_sleep: unlock_mutex::<T>,
        }))
    }

    pub(crate) fn notify_one(&self) {
        unsafe { self.raw.notify_finished_one() };
    }

    pub(crate) unsafe fn notify_one_and_then(&self, after_wake: Option<NotifyFn>) {
        self.raw.notify_finished_one_and_then(after_wake)
    }

    pub(crate) fn notify_one_with_function(
        &self,
        after_wake: Option<NotifyFn>,
        notify_fn: &mut dyn FnMut(TaskHandle, Option<NotifyFn>),
    ) {
        if self.raw.is_blocked() {
            notify_fn(self.raw.get_handle(), after_wake)
        }
    }

    pub(crate) fn notify_one_and_reset(&self, state: &AtomicPtr<Mutex<()>>) {
        fn reset(waiters: usize, data: usize) {
            let state = unsafe { &*(data as *const AtomicPtr<Mutex<()>>) };

            // reset the state of the mutex if we have no more waiters.
            // We can use a relaxed store, as we own a lock to the runtime.
            if waiters == 0 {
                state.store(std::ptr::null_mut(), Ordering::Relaxed)
            }
        }

        let data_ptr = state as *const _ as usize;
        unsafe {
            self.notify_one_and_then(Some(NotifyFn {
                data: data_ptr,
                function: reset,
            }))
        };
    }

    pub(crate) fn notify_all_and_reset(&self, state: &AtomicPtr<Mutex<()>>) {
        fn reset(_: usize, data: usize) {
            let state = unsafe { &*(data as *const AtomicPtr<Mutex<()>>) };

            // reset the state of the mutex.
            // we can use a relaxed store, as we own a lock to the runtime.
            state.store(std::ptr::null_mut(), Ordering::Relaxed)
        }

        let data_ptr = state as *const _ as usize;
        unsafe {
            self.raw.broadcast_finished_and_then(Some(NotifyFn {
                data: data_ptr,
                function: reset,
            }))
        };
    }
}
