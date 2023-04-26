//! Task runtime definition.

use std::error::Error;
use std::fmt::{Debug, Display};
use std::marker::Unsize;
use std::mem::MaybeUninit;
use std::panic::AssertUnwindSafe;
use std::time::Duration;

use fimo_ffi::marshal::CTypeBridge;
use fimo_ffi::ptr::{FetchVTable, ObjInterface};
use fimo_ffi::{interface, DynObj, FfiFn, ObjArc, Vec};

use crate::blockable::IBlockable;
use crate::group::IGroup;

/// Unique identifier of a running task.
///
/// A `TaskId` is a unique identifier for each running task in a runtime.
/// `TaskId`s may be reused after a task has been completed.
#[repr(C)]
#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, PartialEq, Eq, CTypeBridge)]
pub struct TaskId(pub usize);

impl Display for TaskId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Helper type to wrap around a C type.
#[repr(C)]
#[derive(Debug, CTypeBridge)]
pub struct CType<T>
where
    T: CTypeBridge,
{
    val: T::Type,
}

impl<T> CType<T>
where
    T: CTypeBridge,
{
    /// Constructs a new instance.
    pub fn new(val: T) -> Self {
        Self { val: val.marshal() }
    }

    /// Demarshals the value.
    pub fn unwrap(self) -> T {
        unsafe { T::demarshal(self.val) }
    }
}

/// FFI-compatible duration type.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, CTypeBridge)]
pub struct CDuration {
    secs: u64,
    nanos: u32,
}

impl From<Duration> for CDuration {
    fn from(value: Duration) -> Self {
        Self {
            secs: value.as_secs(),
            nanos: value.subsec_nanos(),
        }
    }
}

impl From<CDuration> for Duration {
    fn from(value: CDuration) -> Self {
        let sec = Duration::from_secs(value.secs);
        let subsec_nanos = Duration::from_nanos(value.nanos as u64);
        sec + subsec_nanos
    }
}

/// Error that occurs when trying to use a synchronization operation
/// from a thread that is unable to.
#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default, CTypeBridge)]
pub struct NotOwnedError {
    _v: u8,
}

impl Debug for NotOwnedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "Thread {:?} is not part of the runtime",
            std::thread::current().id()
        )
    }
}

impl Display for NotOwnedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "Thread {:?} is not part of the runtime",
            std::thread::current().name().unwrap_or("unnamed")
        )
    }
}

impl Error for NotOwnedError {}

/// Data passed to a task upon wakeup.
#[repr(C, u8)]
#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, PartialEq, Eq, CTypeBridge)]
pub enum ParkResult {
    /// The wait operation was skipped by the runtime.
    Invalid,
    /// The wait operation timed out.
    TimedOut,
    /// Task was unparked by another task with the given token.
    Unparked(UnparkToken),
}

/// A token associated with a parking task.
#[repr(transparent)]
#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, PartialEq, Eq, CTypeBridge)]
pub struct ParkToken(pub *const ());

/// Result of a notify operation.
#[repr(C)]
#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, PartialEq, Eq, Default, CTypeBridge)]
pub struct UnparkResult {
    /// Number of tasks notified by the operation.
    pub unparked_tasks: usize,
    /// The number of tasks that were requeued.
    pub requeued_tasks: usize,
    /// Whether there are any tasks remaining in the queue.
    /// This only returns true if a thread was unparked.
    pub have_more_tasks: bool,
    /// Indicates whether a fair unlocking mechanism should be used.
    pub be_fair: bool,
}

/// A token which is passed from the unparking task to the
/// unparked task.
#[repr(transparent)]
#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, PartialEq, Eq, CTypeBridge)]
pub struct UnparkToken(pub *const ());

/// Operation that `unpark_filter` should perform for each task.
#[repr(u8)]
#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, PartialEq, Eq, CTypeBridge)]
pub enum UnparkFilterOp {
    /// Unparks the task and continues the filter operation.
    Unpark,
    /// Stops the filter operation without notifying the task.
    Stop,
    /// Continues the filter operation without notifying the task.
    Skip,
}

/// Operation that `unpark_requeue` should perform.
#[repr(u8)]
#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, PartialEq, Eq, CTypeBridge)]
pub enum RequeueOp {
    /// Abort the operation without doing anything.
    Abort,
    /// Unpark one task and requeue the rest onto the target queue.
    UnparkOneRequeueRest,
    /// Requeue all tasks onto the target queue.
    RequeueAll,
    /// Unpark one task and leave the rest parked. No requeuing is done.
    UnparkOne,
    /// Requeue one task and leave the rest parked on the original queue.
    RequeueOne,
}

interface! {
    #![interface_cfg(
        abi(explicit(abi = "C-unwind")),
        uuid = "36c4a496-dbf4-4293-b727-be5aa10fa9d0",
    )]

    /// Interface of a basic fence.
    pub interface IFence: marker Sync {
        /// Signals the fence.
        fn signal(&self);

        /// Returns a pointer to the block list.
        ///
        /// The pointer can be dereferenced, if the caller can
        /// guarantee that there are no other mutable references
        /// to the same object.
        fn block_list(&self) -> *mut DynObj<dyn IBlockable>;
    }
}

interface! {
    #![interface_cfg(
        abi(explicit(abi = "C-unwind")),
        uuid = "164b5afe-950c-49e3-9154-df63d5009673",
    )]

    /// Interface of a runtime.
    pub interface IRuntime: marker Sync {
        /// Checks whether the current thread is owned by
        /// the runtime.
        fn is_owned_by(&self) -> bool;

        /// Id of the current task.
        fn current_task_id(&self) -> Result<TaskId, NotOwnedError>;

        /// Fetches a reference to the group that owns
        /// the current task.
        fn current_group(&self)
            -> Result<&DynObj<dyn IGroup + '_>, NotOwnedError>;

        /// Yields the current task, allowing other tasks of the
        /// group to be run.
        fn yield_now(&self) -> Result<(), NotOwnedError>;

        /// Puts the current task to sleep for at least the specified
        /// amount of time.
        ///
        /// The task may sleep longer than the specified duration, but
        /// never less.
        fn sleep(&self, duration: CDuration) -> Result<(), NotOwnedError>;

        /// Fetches a copy of all groups contained in the runtime.
        fn groups<'a>(&'a self) -> Vec<ObjArc<DynObj<dyn IGroup + 'a>>>;

        /// Fetches a pointer to a value associated with the key, for the
        /// current task.
        ///
        /// The value is lazily initialized on first access from the task,
        /// and is destroyed when the task exits.
        ///
        /// # Safety
        ///
        /// Neither `init` nor `drop` is allowed to panic or call into the
        /// runtime. Furthermore, `key` must be unique and the value must
        /// have a `'static` lifetime bound, and implement `Send`.
        unsafe fn get_or_init_tls_key_impl(
            &self,
            key: *const (),
            init: FfiFn<'_, dyn FnOnce() -> *mut () + '_>,
            drop: unsafe extern "C" fn(*mut ())
        ) -> Result<*const (), NotOwnedError>;

        /// Executes an operation in the runtime thread after
        /// the fence has been signaled.
        ///
        /// # Safety
        ///
        /// The fence and operation pointers mus remain valid until
        /// the fence has been signaled.
        unsafe fn execute_after_completion_impl(
            &self,
            after: *const DynObj<dyn IFence + '_>,
            operation: FfiFn<'_, dyn FnOnce() + Send + '_>,
        );

        /// Waits until the fence has been signaled.
        ///
        /// This operation can be used synchronize with the
        /// completion of all operations, which take a fence
        /// as an optional parameter.
        ///
        /// Can only be called from a thread that is part of
        /// the runtime.
        ///
        /// # Safety
        ///
        /// The fence must have been used with exactly one
        /// operation and must not have been moved in the
        /// meantime.
        unsafe fn wait_on_fence_impl(
            &self,
            fence: *const DynObj<dyn IFence + '_>
        ) -> Result<(), NotOwnedError>;

        /// Parks the current task in the queue associated with the given key.
        ///
        /// The `validate` function is called while the queue is locked and can abort
        /// the operation by returning false. If `validate` returns true then the
        /// current task is appended to the queue and the queue is unlocked.
        ///
        /// The `before_sleep` function is called after the queue is unlocked but before
        /// the task is put to sleep. The task will then sleep until it is unparked
        /// or the given timeout is reached.
        ///
        /// The `timed_out` function is also called while the queue is locked, but only
        /// if the timeout was reached. It is passed the key of the queue it was in when
        /// it timed out, which may be different from the original key if
        /// `unpark_requeue` was called. It is also passed a bool which indicates
        /// whether it was the last task in the queue.
        ///
        /// # Safety
        ///
        /// You should only call this function with an address that you control, since
        /// you could otherwise interfere with the operation of other synchronization
        /// primitives.
        ///
        /// The `validate` and `timed_out` functions are called while the queue is
        /// locked and must not panic or call into any function in [`ParkingLot`].
        ///
        /// The `before_sleep` function is called outside the queue lock and is allowed
        /// to call `unpark_one`, `unpark_all`, `unpark_requeue` or `unpark_filter`, but
        /// it is not allowed to call `park_conditionally` or panic.
        unsafe fn park_conditionally_impl(
            &self,
            key: *const (),
            validate: FfiFn<'_, dyn FnOnce() -> bool + '_>,
            before_sleep: FfiFn<'_, dyn FnOnce() + '_>,
            timed_out: FfiFn<'_, dyn FnOnce(*const (), bool) + '_>,
            park_token: ParkToken,
            timeout: Option<CDuration>,
        ) -> ParkResult;

        /// Unparks one task from the queue associated with the given key.
        ///
        /// The `callback` function is called while the queue is locked and before the
        /// target task is woken up. The [`UnparkResult`] argument to the function
        /// indicates whether a task was found in the queue and whether this was the
        /// last task in the queue. This value is also returned by `unpark_one`.
        ///
        /// The `callback` function should return an [`UnparkToken`] value which will be
        /// passed to the task that is unparked. If no task is unparked then the
        /// returned value is ignored.
        ///
        /// # Safety
        ///
        /// You should only call this function with an address that you control, since
        /// you could otherwise interfere with the operation of other synchronization
        /// primitives.
        ///
        /// The `callback` function is called while the queue is locked and must not
        /// panic or call into any function in [`ParkingLot`].
        ///
        /// The [`ParkingLot`] functions are not re-entrant and calling this method
        /// from the context of an asynchronous signal handler may result in undefined
        /// behavior, including corruption of internal state and/or deadlocks.
        unsafe fn unpark_one_impl(
            &self,
            key: *const (),
            callback: FfiFn<'_, dyn FnOnce(UnparkResult) -> UnparkToken + '_>,
        ) -> UnparkResult;

        /// Unparks all tasks in the queue associated with the given key.
        ///
        /// The given [`UnparkToken`] is passed to all unparked tasks.
        ///
        /// This function returns the number of tasks that were unparked.
        ///
        /// # Safety
        ///
        /// You should only call this function with an address that you control, since
        /// you could otherwise interfere with the operation of other synchronization
        /// primitives.
        ///
        /// The [`ParkingLot`] functions are not re-entrant and calling this method
        /// from the context of an asynchronous signal handler may result in undefined
        /// behavior, including corruption of internal state and/or deadlocks.
        unsafe fn unpark_all_impl(&self, key: *const (), unpark_token: UnparkToken) -> usize;

        /// Removes all tasks from the queue associated with `key_from`, optionally
        /// unparks the first one and requeues the rest onto the queue associated with
        /// `key_to`.
        ///
        /// The `validate` function is called while both queues are locked. Its return
        /// value will determine which operation is performed, or whether the operation
        /// should be aborted. See [`RequeueOp`] for details about the different possible
        /// return values.
        ///
        /// The `callback` function is also called while both queues are locked. It is
        /// passed the [`RequeueOp`] returned by `validate` and an [`UnparkResult`]
        /// indicating whether a task was unparked and whether there are tasks still
        /// parked in the new queue. This [`UnparkResult`] value is also returned by
        /// `unpark_requeue`.
        ///
        /// The `callback` function should return an [`UnparkToken`] value which will be
        /// passed to the task that is unparked. If no task is unparked then the
        /// returned value is ignored.
        ///
        /// # Safety
        ///
        /// You should only call this function with an address that you control, since
        /// you could otherwise interfere with the operation of other synchronization
        /// primitives.
        ///
        /// The `validate` and `callback` functions are called while the queue is locked
        /// and must not panic or call into any function in [`ParkingLot`].
        unsafe fn unpark_requeue_impl(
            &self,
            key_from: *const (),
            key_to: *const (),
            validate: FfiFn<'_, dyn FnOnce() -> RequeueOp + '_>,
            callback: FfiFn<'_, dyn FnOnce(RequeueOp, UnparkResult) -> UnparkToken + '_>,
        ) -> UnparkResult;

        /// Unparks a number of tasks from the front of the queue associated with
        /// `key` depending on the results of a filter function which inspects the
        /// `ParkToken` associated with each task.
        ///
        /// The `filter` function is called for each task in the queue or until
        /// [`UnparkFilterOp::Stop`] is returned. This function is passed the [`ParkToken`]
        /// associated with a particular task, which is unparked if [`UnparkFilterOp::Unpark`]
        /// is returned.
        ///
        /// The `callback` function is also called while both queues are locked. It is
        /// passed an [`UnparkResult`] indicating the number of tasks that were unparked
        /// and whether there are still parked tasks in the queue. This [`UnparkResult`]
        /// value is also returned by `unpark_filter`.
        ///
        /// The `callback` function should return an [`UnparkToken`] value which will be
        /// passed to all tasks that are unparked. If no task is unparked then the
        /// returned value is ignored.
        ///
        /// # Safety
        ///
        /// You should only call this function with an address that you control, since
        /// you could otherwise interfere with the operation of other synchronization
        /// primitives.
        ///
        /// The `filter` and `callback` functions are called while the queue is locked
        /// and must not panic or call into any function in [`ParkingLot`].
        unsafe fn unpark_filter_impl(
            &self,
            key: *const (),
            filter: FfiFn<'_, dyn FnOnce(ParkToken) -> UnparkFilterOp + '_>,
            callback: FfiFn<'_, dyn FnOnce(UnparkResult) -> UnparkToken + '_>,
        ) -> UnparkResult;
    }
}

/// Helper trait for accessing the parking lot of a [`IRuntime`].
pub trait ParkingLot: IRuntime {
    /// Parks the current task in the queue associated with the given key.
    ///
    /// The `validate` function is called while the queue is locked and can abort
    /// the operation by returning false. If `validate` returns true then the
    /// current task is appended to the queue and the queue is unlocked.
    ///
    /// The `before_sleep` function is called after the queue is unlocked but before
    /// the task is put to sleep. The task will then sleep until it is unparked
    /// or the given timeout is reached.
    ///
    /// The `timed_out` function is also called while the queue is locked, but only
    /// if the timeout was reached. It is passed the key of the queue it was in when
    /// it timed out, which may be different from the original key if
    /// `unpark_requeue` was called. It is also passed a bool which indicates
    /// whether it was the last task in the queue.
    ///
    /// # Safety
    ///
    /// You should only call this function with an address that you control, since
    /// you could otherwise interfere with the operation of other synchronization
    /// primitives.
    ///
    /// The `validate` and `timed_out` functions are called while the queue is
    /// locked and must not panic or call into any function in [`ParkingLot`].
    ///
    /// The `before_sleep` function is called outside the queue lock and is allowed
    /// to call `unpark_one`, `unpark_all`, `unpark_requeue` or `unpark_filter`, but
    /// it is not allowed to call `park_conditionally` or panic.
    unsafe fn park_conditionally(
        &self,
        key: *const (),
        validate: impl FnOnce() -> bool,
        before_sleep: impl FnOnce(),
        timed_out: impl FnOnce(*const (), bool),
        park_token: ParkToken,
        timeout: Option<Duration>,
    ) -> ParkResult;

    /// Unparks one task from the queue associated with the given key.
    ///
    /// The `callback` function is called while the queue is locked and before the
    /// target task is woken up. The [`UnparkResult`] argument to the function
    /// indicates whether a task was found in the queue and whether this was the
    /// last task in the queue. This value is also returned by `unpark_one`.
    ///
    /// The `callback` function should return an [`UnparkToken`] value which will be
    /// passed to the task that is unparked. If no task is unparked then the
    /// returned value is ignored.
    ///
    /// # Safety
    ///
    /// You should only call this function with an address that you control, since
    /// you could otherwise interfere with the operation of other synchronization
    /// primitives.
    ///
    /// The `callback` function is called while the queue is locked and must not
    /// panic or call into any function in [`ParkingLot`].
    ///
    /// The [`ParkingLot`] functions are not re-entrant and calling this method
    /// from the context of an asynchronous signal handler may result in undefined
    /// behavior, including corruption of internal state and/or deadlocks.
    unsafe fn unpark_one(
        &self,
        key: *const (),
        callback: impl FnOnce(UnparkResult) -> UnparkToken,
    ) -> UnparkResult;

    /// Unparks all tasks in the queue associated with the given key.
    ///
    /// The given [`UnparkToken`] is passed to all unparked tasks.
    ///
    /// This function returns the number of tasks that were unparked.
    ///
    /// # Safety
    ///
    /// You should only call this function with an address that you control, since
    /// you could otherwise interfere with the operation of other synchronization
    /// primitives.
    ///
    /// The [`ParkingLot`] functions are not re-entrant and calling this method
    /// from the context of an asynchronous signal handler may result in undefined
    /// behavior, including corruption of internal state and/or deadlocks.
    unsafe fn unpark_all(&self, key: *const (), unpark_token: UnparkToken) -> usize;

    /// Removes all tasks from the queue associated with `key_from`, optionally
    /// unparks the first one and requeues the rest onto the queue associated with
    /// `key_to`.
    ///
    /// The `validate` function is called while both queues are locked. Its return
    /// value will determine which operation is performed, or whether the operation
    /// should be aborted. See [`RequeueOp`] for details about the different possible
    /// return values.
    ///
    /// The `callback` function is also called while both queues are locked. It is
    /// passed the [`RequeueOp`] returned by `validate` and an [`UnparkResult`]
    /// indicating whether a task was unparked and whether there are tasks still
    /// parked in the new queue. This [`UnparkResult`] value is also returned by
    /// `unpark_requeue`.
    ///
    /// The `callback` function should return an [`UnparkToken`] value which will be
    /// passed to the task that is unparked. If no task is unparked then the
    /// returned value is ignored.
    ///
    /// # Safety
    ///
    /// You should only call this function with an address that you control, since
    /// you could otherwise interfere with the operation of other synchronization
    /// primitives.
    ///
    /// The `validate` and `callback` functions are called while the queue is locked
    /// and must not panic or call into any function in [`ParkingLot`].
    unsafe fn unpark_requeue(
        &self,
        key_from: *const (),
        key_to: *const (),
        validate: impl FnOnce() -> RequeueOp,
        callback: impl FnOnce(RequeueOp, UnparkResult) -> UnparkToken,
    ) -> UnparkResult;

    /// Unparks a number of tasks from the front of the queue associated with
    /// `key` depending on the results of a filter function which inspects the
    /// `ParkToken` associated with each task.
    ///
    /// The `filter` function is called for each task in the queue or until
    /// [`UnparkFilterOp::Stop`] is returned. This function is passed the [`ParkToken`]
    /// associated with a particular task, which is unparked if [`UnparkFilterOp::Unpark`]
    /// is returned.
    ///
    /// The `callback` function is also called while both queues are locked. It is
    /// passed an [`UnparkResult`] indicating the number of tasks that were unparked
    /// and whether there are still parked tasks in the queue. This [`UnparkResult`]
    /// value is also returned by `unpark_filter`.
    ///
    /// The `callback` function should return an [`UnparkToken`] value which will be
    /// passed to all tasks that are unparked. If no task is unparked then the
    /// returned value is ignored.
    ///
    /// # Safety
    ///
    /// You should only call this function with an address that you control, since
    /// you could otherwise interfere with the operation of other synchronization
    /// primitives.
    ///
    /// The `filter` and `callback` functions are called while the queue is locked
    /// and must not panic or call into any function in [`ParkingLot`].
    unsafe fn unpark_filter(
        &self,
        key: *const (),
        filter: impl FnOnce(ParkToken) -> UnparkFilterOp,
        callback: impl FnOnce(UnparkResult) -> UnparkToken,
    ) -> UnparkResult;
}

impl<T: ?Sized> ParkingLot for T
where
    T: IRuntime,
{
    unsafe fn park_conditionally(
        &self,
        key: *const (),
        validate: impl FnOnce() -> bool,
        before_sleep: impl FnOnce(),
        timed_out: impl FnOnce(*const (), bool),
        park_token: ParkToken,
        timeout: Option<Duration>,
    ) -> ParkResult {
        let mut validate = MaybeUninit::new(validate);
        let validate = FfiFn::new_value(&mut validate);

        let mut before_sleep = MaybeUninit::new(before_sleep);
        let before_sleep = FfiFn::new_value(&mut before_sleep);

        let mut timed_out = MaybeUninit::new(timed_out);
        let timed_out = FfiFn::new_value(&mut timed_out);

        let timeout = timeout.map(Into::into);
        self.park_conditionally_impl(key, validate, before_sleep, timed_out, park_token, timeout)
    }

    unsafe fn unpark_one(
        &self,
        key: *const (),
        callback: impl FnOnce(UnparkResult) -> UnparkToken,
    ) -> UnparkResult {
        let mut callback = MaybeUninit::new(callback);
        let callback = FfiFn::new_value(&mut callback);
        self.unpark_one_impl(key, callback)
    }

    unsafe fn unpark_all(&self, key: *const (), unpark_token: UnparkToken) -> usize {
        self.unpark_all_impl(key, unpark_token)
    }

    unsafe fn unpark_requeue(
        &self,
        key_from: *const (),
        key_to: *const (),
        validate: impl FnOnce() -> RequeueOp,
        callback: impl FnOnce(RequeueOp, UnparkResult) -> UnparkToken,
    ) -> UnparkResult {
        let mut validate = MaybeUninit::new(validate);
        let validate = FfiFn::new_value(&mut validate);

        let mut callback = MaybeUninit::new(callback);
        let callback = FfiFn::new_value(&mut callback);
        self.unpark_requeue_impl(key_from, key_to, validate, callback)
    }

    unsafe fn unpark_filter(
        &self,
        key: *const (),
        filter: impl FnOnce(ParkToken) -> UnparkFilterOp,
        callback: impl FnOnce(UnparkResult) -> UnparkToken,
    ) -> UnparkResult {
        let mut filter = MaybeUninit::new(filter);
        let filter = FfiFn::new_value(&mut filter);

        let mut callback = MaybeUninit::new(callback);
        let callback = FfiFn::new_value(&mut callback);
        self.unpark_filter_impl(key, filter, callback)
    }
}

/// Helper trait for a [`IRuntime`].
pub trait Runtime: IRuntime {
    /// Puts the current task to sleep for at least the specified
    /// amount of time.
    ///
    /// The task may sleep longer than the specified duration, but
    /// never less.
    fn sleep(&self, duration: Duration) -> Result<(), NotOwnedError>;

    /// Fetches a pointer to a value associated with the key, for the
    /// current task.
    ///
    /// The value is lazily initialized on first access from the task,
    /// and is destroyed when the task exits.
    ///
    /// # Safety
    ///
    /// The `key` must be unique.
    unsafe fn get_or_init_tls_key<T: 'static + Send>(
        &self,
        key: *const (),
        init: impl FnOnce() -> T,
    ) -> Result<*const T, NotOwnedError>;

    /// Executes an operation in the runtime thread after the fence
    /// has been signaled.
    ///
    /// # Safety
    ///
    /// The fence and operation pointers mus remain valid until
    /// the fence has been signaled.
    unsafe fn execute_after_completion<'a, F>(
        &self,
        after: *const F,
        operation: impl FnOnce() + Send,
    ) where
        F: FetchVTable<<(dyn IFence + 'a) as ObjInterface<'a>>::Base> + Unsize<dyn IFence + 'a>;

    /// Waits until the fence has been signaled.
    ///
    /// This operation can be used synchronize with the completion of
    /// all operations, which take a fence as an optional parameter.
    ///
    /// Can only be called from a thread that is part of the runtime.
    ///
    /// # Safety
    ///
    /// The fence must have been used with exactly one operation and
    /// must not have been moved in the meantime.
    unsafe fn wait_on_fence<'a, F>(&self, fence: *const F) -> Result<(), NotOwnedError>
    where
        F: FetchVTable<<(dyn IFence + 'a) as ObjInterface<'a>>::Base> + Unsize<dyn IFence + 'a>;
}

impl<R> Runtime for R
where
    R: IRuntime + ?Sized,
{
    fn sleep(&self, duration: Duration) -> Result<(), NotOwnedError> {
        self.sleep(duration.into())
    }

    unsafe fn get_or_init_tls_key<T: 'static + Send>(
        &self,
        key: *const (),
        init: impl FnOnce() -> T,
    ) -> Result<*const T, NotOwnedError> {
        unsafe extern "C" fn __drop<T: 'static>(ptr: *mut ()) {
            let ptr = ptr as *mut T;
            let _ = Box::from_raw(ptr);
        }

        let mut res = MaybeUninit::uninit();
        let res_ref = &mut res;
        let mut init_cl = MaybeUninit::new(move || {
            let res = std::panic::catch_unwind(AssertUnwindSafe(move || {
                let init = init();
                Box::into_raw(Box::new(init))
            }));

            match res {
                Ok(ptr) => {
                    res_ref.write(Ok(()));
                    ptr as *mut ()
                }
                Err(e) => {
                    res_ref.write(Err(e));
                    std::ptr::null_mut()
                }
            }
        });
        let init = unsafe { fimo_ffi::FfiFn::new_value(&mut init_cl) };
        let drop = __drop::<T> as unsafe extern "C" fn(*mut ());

        let ptr = unsafe { self.get_or_init_tls_key_impl(key, init, drop)? };
        match res.assume_init() {
            Ok(()) => Ok(ptr.cast()),
            Err(e) => std::panic::resume_unwind(e),
        }
    }

    unsafe fn execute_after_completion<'a, F>(
        &self,
        after: *const F,
        operation: impl FnOnce() + Send,
    ) where
        F: FetchVTable<<(dyn IFence + 'a) as ObjInterface<'a>>::Base> + Unsize<dyn IFence + 'a>,
    {
        let after = fimo_ffi::ptr::coerce_obj_raw(after);
        let operation = FfiFn::r#box(Box::new(operation));
        self.execute_after_completion_impl(after, operation)
    }

    unsafe fn wait_on_fence<'a, F>(&self, fence: *const F) -> Result<(), NotOwnedError>
    where
        F: FetchVTable<<(dyn IFence + 'a) as ObjInterface<'a>>::Base> + Unsize<dyn IFence + 'a>,
    {
        let fence = fimo_ffi::ptr::coerce_obj_raw(fence);
        self.wait_on_fence_impl(fence)
    }
}
