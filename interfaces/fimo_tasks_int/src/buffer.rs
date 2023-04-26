//! Implementation of task buffers.
use std::cell::UnsafeCell;
use std::error::Error;
use std::fmt::{Debug, Display};
use std::marker::{PhantomPinned, Unsize};
use std::mem::MaybeUninit;
use std::pin::Pin;
use std::sync::atomic::AtomicBool;

use fimo_ffi::marshal::CTypeBridge;
use fimo_ffi::ptr::{FetchVTable, ObjInterface};
use fimo_ffi::span::ConstSpanPtr;
use fimo_ffi::{DynObj, Object};

use crate::blockable::{IBlockable, WaitList};
use crate::runtime2::{IFence, IRuntime, Runtime};
use crate::task2::ITask;

/// An entry of a task buffer.
#[repr(C, i32)]
#[derive(Clone, Copy, CTypeBridge)]
pub enum TaskBufferEntry<'a> {
    /// A task that must be executed.
    Task(<*const DynObj<dyn ITask + 'a> as CTypeBridge>::Type) = 0,
    /// A synchronization barrier.
    Barrier = 1,
}

impl Debug for TaskBufferEntry<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Task(arg0) => f
                .debug_tuple("Task")
                .field(unsafe { &<*const DynObj<dyn ITask + '_> as CTypeBridge>::demarshal(*arg0) })
                .finish(),
            Self::Barrier => write!(f, "Barrier"),
        }
    }
}

/// A task buffer.
#[repr(C)]
#[derive(Clone, Copy, CTypeBridge)]
pub struct RawTaskBuffer<'a> {
    /// Buffer of tasks.
    pub buffer: ConstSpanPtr<TaskBufferEntry<'a>>,
    /// Fence to signal the completion of all commands in the buffer.
    pub fence: <*const DynObj<dyn IFence + 'a> as CTypeBridge>::Type,
}

impl Debug for RawTaskBuffer<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RawTaskBuffer")
            .field("buffer", &self.buffer)
            .field("fence", unsafe {
                &<*const DynObj<dyn IFence> as CTypeBridge>::demarshal(self.fence)
            })
            .finish()
    }
}

#[derive(Debug)]
enum TaskBufferEntryImpl<T> {
    Task(T),
    Barrier,
}

#[derive(Debug, Object)]
#[interfaces(IFence)]
enum Fence {
    OsFence {
        waiters: UnsafeCell<WaiterList>,
        condvar: std::sync::Condvar,
        signaled: std::sync::Mutex<bool>,
    },
    TaskFence {
        signaled: AtomicBool,
        waiters: UnsafeCell<WaiterList>,
    },
}

unsafe impl Sync for Fence {}

#[derive(Debug, Object, Default)]
#[interfaces(IBlockable)]
struct WaiterList(WaitList);

impl IBlockable for WaiterList {
    fn waiter_list(&self) -> &DynObj<dyn crate::blockable::IWaitList> {
        fimo_ffi::ptr::coerce_obj(&self.0)
    }

    fn waiter_list_mut(&mut self) -> &mut DynObj<dyn crate::blockable::IWaitList> {
        fimo_ffi::ptr::coerce_obj_mut(&mut self.0)
    }

    fn dependency_list(&self) -> Option<&DynObj<dyn crate::blockable::IWaitList>> {
        None
    }

    fn dependecy_list_mut(&mut self) -> Option<&mut DynObj<dyn crate::blockable::IWaitList>> {
        None
    }
}

impl IFence for Fence {
    fn signal(&self) {
        match self {
            Fence::OsFence {
                condvar, signaled, ..
            } => {
                let mut guard = signaled.lock().unwrap();
                *guard = true;
                condvar.notify_all();
            }
            Fence::TaskFence { signaled, .. } => {
                signaled.store(true, std::sync::atomic::Ordering::Release)
            }
        }
    }

    fn block_list(&self) -> *mut DynObj<dyn IBlockable> {
        match self {
            Fence::OsFence { waiters, .. } => fimo_ffi::ptr::coerce_obj_mut_raw(waiters.get()),
            Fence::TaskFence { waiters, .. } => fimo_ffi::ptr::coerce_obj_mut_raw(waiters.get()),
        }
    }
}

/// A buffer with a statically bound number of tasks, stored on the stack.
pub struct BoundedTaskBuffer<'a, 'b, T, const N: usize> {
    num_entries: usize,
    fence: Option<Fence>,
    runtime: Option<&'b DynObj<dyn IRuntime + 'b>>,
    entries: [MaybeUninit<TaskBufferEntryImpl<T>>; N],
    entry_pointers: [MaybeUninit<TaskBufferEntry<'a>>; N],
    _pinned: PhantomPinned,
}

impl<T, const N: usize> BoundedTaskBuffer<'_, '_, T, N> {
    /// Constructs a new buffer.
    pub fn new() -> Self {
        Self {
            num_entries: 0,
            fence: None,
            runtime: None,
            entries: MaybeUninit::uninit_array(),
            entry_pointers: MaybeUninit::uninit_array(),
            _pinned: PhantomPinned,
        }
    }

    /// Checks if the buffer was submitted.
    pub fn is_submitted(&self) -> bool {
        self.runtime.is_some()
    }

    /// Checks if all commands inside the buffer have been completed.
    pub fn is_completed(&self) -> bool {
        if let Some(fence) = &self.fence {
            match fence {
                Fence::OsFence { signaled, .. } => *signaled.lock().unwrap(),
                Fence::TaskFence { signaled, .. } => {
                    signaled.load(std::sync::atomic::Ordering::Acquire)
                }
            }
        } else {
            false
        }
    }

    /// Checks if the buffer is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Number of commands.
    pub fn len(&self) -> usize {
        self.num_entries
    }

    /// Capacity of the buffer.
    pub fn capacity(&self) -> usize {
        N
    }

    /// Pushes a barrier into the buffer.
    ///
    /// A barrier ensures that all prior tasks are completed before starting subsequent tasks.
    /// It is allowed, that the number of commands remains unchanged, if it can be determined that
    /// a barrier would not result in any observable effect.
    ///
    /// # Panic
    ///
    /// The operation panics if the capacity is not big enough to contain another command,
    /// or if the buffer is already submitted.
    pub fn push_barrier(&mut self) {
        self.try_push_barrier()
            .expect_err("Can not push a barrier into the buffer");
    }

    /// Pushes a task into the buffer.
    ///
    /// The start of the task is synchronized with the last barrier present in the buffer.
    ///
    /// # Panic
    ///
    /// The operation panics if the capacity is not big enough to contain another command,
    /// or if the buffer is already submitted.
    pub fn push_task(&mut self, task: T) {
        self.try_push_task(task)
            .expect_err("Can not push a task into the buffer");
    }

    /// Pushes an array of tasks into the buffer.
    ///
    /// The start of the tasks is synchronized with the last barrier present in the buffer.
    ///
    /// # Panic
    ///
    /// The operation panics if the capacity is not big enough to contain all task,
    /// or if the buffer is already submitted.
    pub fn push_task_array<const M: usize>(&mut self, tasks: [T; M]) {
        self.try_push_task_array(tasks)
            .expect_err("Can not push all tasks into the buffer");
    }

    /// Tries pushing a barrier into the buffer.
    ///
    /// A barrier ensures that all prior tasks are completed before starting subsequent tasks.
    /// It is allowed, that the number of commands remains unchanged, if it can be determined that
    /// a barrier would not result in any observable effect.
    ///
    /// The function will fail if the capacity if not enough to contain another command,
    /// or if the buffer is already submitted.
    pub fn try_push_barrier(&mut self) -> Result<(), BufferFullError<()>> {
        if self.len() == self.capacity() || self.is_submitted() {
            Err(BufferFullError(()))
        } else if !self.is_empty() {
            // Safety: We know that the the range 0..self.len() is always initialized.
            match unsafe { self.entries[self.len() - 1].assume_init_ref() } {
                TaskBufferEntryImpl::Task(_) => {
                    self.entries[self.len()].write(TaskBufferEntryImpl::Barrier);
                    self.num_entries += 1;
                }
                TaskBufferEntryImpl::Barrier => {}
            }
            Ok(())
        } else {
            Ok(())
        }
    }

    /// Tries pushing a task into the buffer.
    ///
    /// The start of the task is synchronized with the last barrier present in the buffer.
    ///
    /// The function will fail if the capacity if not enough to contain another command,
    /// or if the buffer is already submitted.
    pub fn try_push_task(&mut self, task: T) -> Result<(), BufferFullError<T>> {
        if self.len() == self.capacity() || self.is_submitted() {
            Err(BufferFullError(task))
        } else {
            self.entries[self.len()].write(TaskBufferEntryImpl::Task(task));
            self.num_entries += 1;
            Ok(())
        }
    }

    /// Tries pushing an array of tasks into the buffer.
    ///
    /// The start of the tasks is synchronized with the last barrier present in the buffer.
    ///
    /// The function will fail if the capacity if not enough to contain all task commands,
    /// or if the buffer is already submitted.
    pub fn try_push_task_array<const M: usize>(
        &mut self,
        tasks: [T; M],
    ) -> Result<(), BufferFullError<[T; M]>> {
        if self.len() + M >= self.capacity() || self.is_submitted() {
            Err(BufferFullError(tasks))
        } else {
            for task in tasks {
                self.entries[self.len()].write(TaskBufferEntryImpl::Task(task));
                self.num_entries += 1;
            }
            Ok(())
        }
    }

    /// Joins the buffer, waiting for all tasks to be completed.
    ///
    /// Returns the tasks contained in the buffer.
    pub fn join(self: Pin<&mut Self>) -> [Option<T>; N] {
        if self.is_submitted() && !self.is_completed() {
            match self
                .fence
                .as_ref()
                .expect("The fence should be initialized at this point")
            {
                Fence::OsFence {
                    condvar, signaled, ..
                } => {
                    let mut signaled = signaled.lock().unwrap();

                    while !*signaled {
                        signaled = condvar.wait(signaled).unwrap();
                    }
                }
                Fence::TaskFence { .. } => {
                    let runtime = self.runtime.unwrap();
                    let fence = self.fence.as_ref().unwrap();

                    // Safety: We know at this point, that the fence has not been moved.
                    unsafe { runtime.wait_on_fence(fence).unwrap() };
                }
            }
        }

        let num_entries = self.len();
        let mut res = MaybeUninit::uninit_array();

        // Safety: We won't move Self.
        let this = unsafe { Pin::get_unchecked_mut(self) };
        for (i, x) in res.iter_mut().enumerate() {
            if i < num_entries {
                // Safety: We know that the the range 0..len is initialized.
                let entry = unsafe { this.entries[i].assume_init_read() };
                match entry {
                    TaskBufferEntryImpl::Task(t) => x.write(Some(t)),
                    TaskBufferEntryImpl::Barrier => x.write(None),
                };
            } else {
                x.write(None);
            }
        }

        this.num_entries = 0;

        // Safety: We initialized all elements of the array.
        unsafe { MaybeUninit::array_assume_init(res) }
    }
}

impl<T, const N: usize> BoundedTaskBuffer<'static, '_, T, N>
where
    T: Send,
{
    /// Detaches the buffer, so that it can be dropped without waiting for completion.
    pub fn detach(self: Pin<Box<Self>>) {
        // Safety: We know that the buffer lives long enough, because
        // we have a bound of static.
        unsafe { BoundedTaskBuffer::detach_unchecked(self) }
    }
}

impl<T, const N: usize> BoundedTaskBuffer<'_, '_, T, N>
where
    T: Send,
{
    /// Detaches the buffer, so that it can be dropped without waiting for completion.
    ///
    /// # Safety
    ///
    /// The buffer must outlive the signaling of the fence.
    pub unsafe fn detach_unchecked(self: Pin<Box<Self>>) {
        if self.is_submitted() && !self.is_completed() {
            let runtime = self.runtime.unwrap();
            let fence = self.fence.as_ref().unwrap() as *const _;
            let f = move || drop(self);
            runtime.execute_after_completion(fence, f);
        } else {
            drop(self)
        }
    }
}

impl<T, const N: usize> Default for BoundedTaskBuffer<'_, '_, T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Debug, const N: usize> Debug for BoundedTaskBuffer<'_, '_, T, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BoundedTaskBuffer")
            .field("num_entries", &self.num_entries)
            .field("fence", &self.fence)
            .field("runtime", &self.runtime.map(|r| r as *const _))
            .field("entries", &self.entries)
            .field("entry_pointers", &self.entry_pointers)
            .field("_pinned", &self._pinned)
            .finish()
    }
}

impl<T, const N: usize> Drop for BoundedTaskBuffer<'_, '_, T, N> {
    fn drop(&mut self) {
        if self.is_submitted() && !self.is_completed() {
            match self
                .fence
                .as_ref()
                .expect("The fence should be initialized at this point")
            {
                Fence::OsFence {
                    condvar, signaled, ..
                } => {
                    let mut signaled = signaled.lock().unwrap();

                    while !*signaled {
                        signaled = condvar.wait(signaled).unwrap();
                    }
                }
                Fence::TaskFence { .. } => {
                    let runtime = self.runtime.unwrap();
                    let fence = self.fence.as_ref().unwrap();

                    // Safety: We know at this point, that the fence has not been moved.
                    unsafe { runtime.wait_on_fence(fence).unwrap() };
                }
            }
        }

        for entry in &mut self.entries[0..self.num_entries] {
            // Safety: We know that the entry is initialized.
            unsafe { entry.assume_init_drop() };
        }
    }
}

/// Error that occurs when trying to push to a full [`BoundedTaskBuffer`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BufferFullError<T>(T);

impl<T> Debug for BufferFullError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Buffer full")
    }
}

impl<T> Display for BufferFullError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Buffer full")
    }
}

impl<T> Error for BufferFullError<T> {}

/// A buffer which stores the tasks on the heap.
pub struct TaskBuffer<'a, 'b, T> {
    fence: Option<Fence>,
    entries: Vec<TaskBufferEntryImpl<T>>,
    entry_pointers: Vec<TaskBufferEntry<'a>>,
    runtime: Option<&'b DynObj<dyn IRuntime + 'b>>,
    _pinned: PhantomPinned,
}

impl<T> TaskBuffer<'_, '_, T> {
    /// Constructs a new buffer.
    pub fn new() -> Self {
        Self {
            fence: None,
            entries: Default::default(),
            entry_pointers: Default::default(),
            runtime: None,
            _pinned: PhantomPinned,
        }
    }

    /// Checks if the buffer was submitted.
    pub fn is_submitted(&self) -> bool {
        self.runtime.is_some()
    }

    /// Checks if all commands inside the buffer have been completed.
    pub fn is_completed(&self) -> bool {
        if let Some(fence) = &self.fence {
            match fence {
                Fence::OsFence { signaled, .. } => *signaled.lock().unwrap(),
                Fence::TaskFence { signaled, .. } => {
                    signaled.load(std::sync::atomic::Ordering::Acquire)
                }
            }
        } else {
            false
        }
    }

    /// Checks if the buffer is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Number of commands.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Capacity of the buffer.
    pub fn capacity(&self) -> usize {
        self.entries.capacity()
    }

    /// Pushes a barrier into the buffer.
    ///
    /// A barrier ensures that all prior tasks are completed before starting subsequent tasks.
    /// It is allowed, that the number of commands remains unchanged, if it can be determined that
    /// a barrier would not result in any observable effect.
    ///
    /// # Panic
    ///
    /// The operation panics, if the buffer is already submitted.
    pub fn push_barrier(&mut self) {
        self.try_push_barrier()
            .expect_err("Can not push a barrier into the buffer");
    }

    /// Pushes a task into the buffer.
    ///
    /// The start of the task is synchronized with the last barrier present in the buffer.
    ///
    /// # Panic
    ///
    /// The operation panics, if the buffer is already submitted.
    pub fn push_task(&mut self, task: T) {
        self.try_push_task(task)
            .expect_err("Can not push a task into the buffer");
    }

    /// Pushes an array of tasks into the buffer.
    ///
    /// The start of the tasks is synchronized with the last barrier present in the buffer.
    ///
    /// # Panic
    ///
    /// The operation panics, if the buffer is already submitted.
    pub fn push_task_array<const M: usize>(&mut self, tasks: [T; M]) {
        self.try_push_task_array(tasks)
            .expect_err("Can not push all tasks into the buffer");
    }

    /// Tries pushing a barrier into the buffer.
    ///
    /// A barrier ensures that all prior tasks are completed before starting subsequent tasks.
    /// It is allowed, that the number of commands remains unchanged, if it can be determined that
    /// a barrier would not result in any observable effect.
    ///
    /// The function will fail, if the buffer is already submitted.
    pub fn try_push_barrier(&mut self) -> Result<(), BufferFullError<()>> {
        if self.is_submitted() {
            Err(BufferFullError(()))
        } else if let Some(entry) = self.entries.last() {
            if matches!(entry, TaskBufferEntryImpl::Task(_)) {
                self.entries.push(TaskBufferEntryImpl::Barrier);
            }
            Ok(())
        } else {
            Ok(())
        }
    }

    /// Tries pushing a task into the buffer.
    ///
    /// The start of the task is synchronized with the last barrier present in the buffer.
    ///
    /// The function will fail, if the buffer is already submitted.
    pub fn try_push_task(&mut self, task: T) -> Result<(), BufferFullError<T>> {
        if self.is_submitted() {
            Err(BufferFullError(task))
        } else {
            self.entries.push(TaskBufferEntryImpl::Task(task));
            Ok(())
        }
    }

    /// Tries pushing an array of tasks into the buffer.
    ///
    /// The start of the tasks is synchronized with the last barrier present in the buffer.
    ///
    /// The function will fail, if the buffer is already submitted.
    pub fn try_push_task_array<const M: usize>(
        &mut self,
        tasks: [T; M],
    ) -> Result<(), BufferFullError<[T; M]>> {
        self.try_push_task_iter(tasks)
    }

    /// Tries pushing all tasks of a collection into the buffer.
    ///
    /// The start of the tasks is synchronized with the last barrier present in the buffer.
    ///
    /// The function will fail, if the buffer is already submitted.
    pub fn try_push_task_iter<U>(&mut self, iter: U) -> Result<(), BufferFullError<U>>
    where
        U: IntoIterator<Item = T>,
    {
        if self.is_submitted() {
            Err(BufferFullError(iter))
        } else {
            self.entries
                .extend(iter.into_iter().map(TaskBufferEntryImpl::Task));
            Ok(())
        }
    }

    /// Joins the buffer, waiting for all tasks to be completed.
    ///
    /// Returns the tasks contained in the buffer.
    pub fn join(self: Pin<&mut Self>) -> Vec<Option<T>> {
        if self.is_submitted() && !self.is_completed() {
            match self
                .fence
                .as_ref()
                .expect("The fence should be initialized at this point")
            {
                Fence::OsFence {
                    condvar, signaled, ..
                } => {
                    let mut signaled = signaled.lock().unwrap();

                    while !*signaled {
                        signaled = condvar.wait(signaled).unwrap();
                    }
                }
                Fence::TaskFence { .. } => {
                    let runtime = self.runtime.unwrap();
                    let fence = self.fence.as_ref().unwrap();

                    // Safety: We know at this point, that the fence has not been moved.
                    unsafe { runtime.wait_on_fence(fence).unwrap() };
                }
            }
        }

        // Safety: We won't move Self.
        let this = unsafe { Pin::get_unchecked_mut(self) };
        let entries = std::mem::take(&mut this.entries);

        entries
            .into_iter()
            .map(|e| match e {
                TaskBufferEntryImpl::Task(t) => Some(t),
                TaskBufferEntryImpl::Barrier => None,
            })
            .collect()
    }
}

impl<T> TaskBuffer<'static, '_, T>
where
    T: Send,
{
    /// Detaches the buffer, so that it can be dropped without waiting for completion.
    pub fn detach(self: Pin<Box<Self>>) {
        // Safety: We know that the buffer lives long enough, because
        // we have a bound of static.
        unsafe { TaskBuffer::detach_unchecked(self) }
    }
}

impl<T> TaskBuffer<'_, '_, T>
where
    T: Send,
{
    /// Detaches the buffer, so that it can be dropped without waiting for completion.
    ///
    /// # Safety
    ///
    /// The buffer must outlive the signaling of the fence.
    pub unsafe fn detach_unchecked(self: Pin<Box<Self>>) {
        if self.is_submitted() && !self.is_completed() {
            let runtime = self.runtime.unwrap();
            let fence = self.fence.as_ref().unwrap() as *const _;
            let f = move || drop(self);
            runtime.execute_after_completion(fence, f);
        } else {
            drop(self)
        }
    }
}

impl<T> Default for TaskBuffer<'_, '_, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Debug> Debug for TaskBuffer<'_, '_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TaskBuffer")
            .field("fence", &self.fence)
            .field("entries", &self.entries)
            .field("entry_pointers", &self.entry_pointers)
            .field("runtime", &self.runtime.map(|r| r as *const _))
            .field("_pinned", &self._pinned)
            .finish()
    }
}

impl<T> Drop for TaskBuffer<'_, '_, T> {
    fn drop(&mut self) {
        if self.is_submitted() && !self.is_completed() {
            match self
                .fence
                .as_ref()
                .expect("The fence should be initialized at this point")
            {
                Fence::OsFence {
                    condvar, signaled, ..
                } => {
                    let mut signaled = signaled.lock().unwrap();

                    while !*signaled {
                        signaled = condvar.wait(signaled).unwrap();
                    }
                }
                Fence::TaskFence { .. } => {
                    let runtime = self.runtime.unwrap();
                    let fence = self.fence.as_ref().unwrap();

                    // Safety: We know at this point, that the fence has not been moved.
                    unsafe { runtime.wait_on_fence(fence).unwrap() };
                }
            }
        }
    }
}

/// Helper trait for abstracting over the different types of task buffers.
pub trait Submittable<'a, 'b> {
    /// Checks if the buffer is already submitted.
    fn is_submitted(&self) -> bool;

    /// Checks if the buffer contains no commands.
    fn is_empty(&self) -> bool;

    /// Constructs a [`RawTaskBuffer`] from the buffer,
    /// and sets the submitted flag.
    fn confirm_submission(
        self: Pin<&mut Self>,
        runtime: &'b DynObj<dyn IRuntime + 'b>,
    ) -> RawTaskBuffer<'a>;
}

impl<'a, 'b, T, const N: usize> Submittable<'a, 'b> for BoundedTaskBuffer<'a, 'b, T, N>
where
    T: FetchVTable<<dyn ITask + 'a as ObjInterface<'a>>::Base> + Unsize<dyn ITask + 'a>,
{
    fn is_submitted(&self) -> bool {
        self.is_submitted()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    fn confirm_submission(
        self: Pin<&mut Self>,
        runtime: &'b DynObj<dyn IRuntime + 'b>,
    ) -> RawTaskBuffer<'a> {
        assert!(!self.is_submitted());

        // Safety: We won't move out of self.
        let this = unsafe { Pin::get_unchecked_mut(self) };
        this.runtime = Some(runtime);
        this.fence = if runtime.is_owned_by() {
            Some(Fence::TaskFence {
                signaled: Default::default(),
                waiters: Default::default(),
            })
        } else {
            Some(Fence::OsFence {
                waiters: Default::default(),
                condvar: Default::default(),
                signaled: Default::default(),
            })
        };

        for (entry, entry_ptr) in this
            .entries
            .iter()
            .zip(&mut this.entry_pointers)
            .take(this.num_entries)
        {
            // Safety: We know that the range 0..this.num_entries is initialized.
            let entry = unsafe { entry.assume_init_ref() };
            match entry {
                TaskBufferEntryImpl::Task(t) => {
                    let t: *const DynObj<dyn ITask + 'a> = fimo_ffi::ptr::coerce_obj_raw(t);
                    entry_ptr.write(TaskBufferEntry::Task(t.marshal()))
                }
                TaskBufferEntryImpl::Barrier => entry_ptr.write(TaskBufferEntry::Barrier),
            };
        }

        // Safety: We just initialized all required entries.
        let buffer = unsafe {
            let entry_ptrs = &this.entry_pointers[0..this.num_entries];
            let entry_ptrs = MaybeUninit::slice_assume_init_ref(entry_ptrs);
            ConstSpanPtr::from(entry_ptrs)
        };
        let fence = {
            let fence: *const DynObj<dyn IFence> =
                fimo_ffi::ptr::coerce_obj_raw(this.fence.as_ref().unwrap());
            fence.marshal()
        };

        RawTaskBuffer { buffer, fence }
    }
}

impl<'a, 'b, T> Submittable<'a, 'b> for TaskBuffer<'a, 'b, T>
where
    T: FetchVTable<<dyn ITask + 'a as ObjInterface<'a>>::Base> + Unsize<dyn ITask + 'a>,
{
    fn is_submitted(&self) -> bool {
        self.is_submitted()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    fn confirm_submission(
        self: Pin<&mut Self>,
        runtime: &'b DynObj<dyn IRuntime + 'b>,
    ) -> RawTaskBuffer<'a> {
        assert!(!self.is_submitted());

        // Safety: We won't move out of self.
        let this = unsafe { Pin::get_unchecked_mut(self) };
        this.runtime = Some(runtime);
        this.fence = if runtime.is_owned_by() {
            Some(Fence::TaskFence {
                signaled: Default::default(),
                waiters: Default::default(),
            })
        } else {
            Some(Fence::OsFence {
                waiters: Default::default(),
                condvar: Default::default(),
                signaled: Default::default(),
            })
        };

        for entry in &this.entries {
            match entry {
                TaskBufferEntryImpl::Task(t) => {
                    let t: *const DynObj<dyn ITask + 'a> = fimo_ffi::ptr::coerce_obj_raw(t);
                    this.entry_pointers.push(TaskBufferEntry::Task(t.marshal()))
                }
                TaskBufferEntryImpl::Barrier => this.entry_pointers.push(TaskBufferEntry::Barrier),
            };
        }

        let buffer = ConstSpanPtr::from(&*this.entry_pointers);
        let fence = {
            let fence: *const DynObj<dyn IFence> =
                fimo_ffi::ptr::coerce_obj_raw(this.fence.as_ref().unwrap());
            fence.marshal()
        };

        RawTaskBuffer { buffer, fence }
    }
}
