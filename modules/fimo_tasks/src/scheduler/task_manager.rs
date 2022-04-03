use super::stack_allocator::TaskSlot;
use context::Context;
use fimo_ffi::cell::{AtomicRef, AtomicRefCell, AtomicRefMut};
use fimo_ffi::ffi_fn::RawFfiFn;
use fimo_ffi::ptr::IBaseExt;
use fimo_ffi::{DynObj, FfiFn, ObjBox, ObjectId};
use fimo_module::{Error, ErrorKind};
use fimo_tasks_int::raw::{
    AtomicISchedulerContext, IRawTask, IRustPanicData, ISchedulerContext, StatusRequest,
    TaskHandle, TaskPriority, TaskRunStatus, TaskScheduleStatus, WorkerId,
};
use fimo_tasks_int::runtime::IScheduler;
use log::{debug, error, trace};
use std::any::Any;
use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, VecDeque};
use std::fmt::Debug;
use std::ops::RangeFrom;
use std::sync::mpsc::Receiver;
use std::time::SystemTime;

#[derive(Debug)]
pub(crate) struct TaskManager {
    msg_receiver: Receiver<Msg<'static>>,
    handle_iter: RangeFrom<usize>,
    free_handles: VecDeque<TaskHandle>,
    tasks: BTreeMap<TaskHandle, AssertValidTask>,
    processing_queue: BinaryHeap<Reverse<AssertValidTask>>,
}

impl TaskManager {
    pub fn new(msg_receiver: Receiver<Msg<'static>>) -> Self {
        trace!("Initializing the task manager");
        Self {
            msg_receiver,
            handle_iter: 0..,
            free_handles: Default::default(),
            tasks: Default::default(),
            processing_queue: Default::default(),
        }
    }

    fn allocate_handle(&mut self) -> Result<TaskHandle, Error> {
        trace!("Allocating a task handle");

        if let Some(handle) = self.free_handles.pop_front() {
            debug!("Reusing existing handle {}", handle);
            Ok(handle)
        } else {
            trace!("Allocating new handle");
            if let Some(id) = self.handle_iter.next() {
                let handle = TaskHandle { id, generation: 0 };
                debug!("Allocated handle {}", handle);
                Ok(handle)
            } else {
                error!("Handles exhausted");
                let err = "Exhausted all possible handles";
                Err(Error::new(ErrorKind::ResourceExhausted, err))
            }
        }
    }

    /// Frees the handle without increasing the generation allowing it's reallocation.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the provided handle has not been leaked and is
    /// currently allocated. Mainly intended to be used when an error occurs during
    /// a task registration, allowing us to support more tasks before an overflow occurs.
    unsafe fn free_handle_reuse(&mut self, handle: TaskHandle) {
        trace!("Reusing handle {}", handle);

        // pushing it to the back may improve debugging by
        // maximizing the time until the same id is reused.
        self.free_handles.push_back(handle);
    }

    fn free_handle(&mut self, handle: TaskHandle) {
        trace!("Freeing handle {}", handle);

        // discard a handle if the generation reaches the
        // maximum possible value, otherwise push it onto the list.
        if handle.generation == usize::MAX {
            trace!("Discarding handle {}", handle);
        } else {
            trace!("Mark handle {} for reuse", handle);
            let handle = TaskHandle {
                id: handle.id,
                generation: handle.generation + 1,
            };

            // SAFETY: We created a new handle by increasing the generation so
            // we know that it s unique.
            unsafe { self.free_handle_reuse(handle) };
        }
    }

    #[inline]
    pub fn take_messages(&mut self) -> Vec<Msg<'static>> {
        self.msg_receiver.try_iter().collect()
    }

    /// Enqueues a task without changing or checking any flags.
    ///
    /// # Safety
    ///
    /// A task may appear only once in the queue.
    #[inline]
    pub unsafe fn enqueue_unchecked(&mut self, task: AssertValidTask) {
        self.processing_queue.push(Reverse(task))
    }

    /// Enqueues a task if it is able to.
    ///
    /// # Note
    ///
    /// Does nothing if the `processing` or `in_queue` flags in the private
    /// context are set. Sets `in_queue` to `true` in case of success.
    #[inline]
    pub fn enqueue(&mut self, task: AssertValidTask) {
        let context = task.context().borrow();
        debug_assert_eq!(context.schedule_status(), TaskScheduleStatus::Runnable);

        let data = context.scheduler_data();
        let mut private_data = data.private_data_mut();
        if !(private_data.is_processing() || private_data.is_in_queue()) {
            // SAFETY: We insert the task immediately afterwards.
            unsafe { private_data.assert_in_queue() };

            drop(private_data);
            drop(context);

            // SAFETY: this method is behind a mutable reference, so we know
            // that the scheduler lock was acquired and we have unique access
            // to the processing queue. Now we have to ensure that we aren't
            // trying to enqueue a task multiple times. This is done by
            // dynamically checking that the `in_queue` flag is not set. This
            // flag can only be unset during the processing of the queue
            // during scheduling. To remove the need of removing a prematurely
            // inserted task, we disable the operation entirely if the task is
            // being processed.
            unsafe { self.enqueue_unchecked(task) }
        }
    }

    /// Clears the queue and returns it.
    ///
    /// # Safety
    ///
    /// Only callable during scheduling.
    #[inline]
    pub unsafe fn clear_queue(&mut self) -> BinaryHeap<Reverse<AssertValidTask>> {
        std::mem::take(&mut self.processing_queue)
    }

    pub fn find_task(&self, handle: TaskHandle) -> Result<&'static DynObj<dyn IRawTask>, Error> {
        trace!("Searching for task {}", handle);
        if let Some(task) = self.tasks.get(&handle) {
            trace!("Found task");
            Ok(task.0)
        } else {
            error!("Task {} not found", handle);
            let err = format!("Task {} is not registered", handle);
            Err(Error::new(ErrorKind::InvalidArgument, err))
        }
    }

    /// # Safety
    ///
    /// See [`register_task`](fimo_tasks_int::runtime::IScheduler::register_task)
    pub unsafe fn register_task(
        &mut self,
        task: &DynObj<dyn IRawTask + '_>,
        wait_on: &[TaskHandle],
    ) -> Result<(), Error> {
        trace!("Registering new task {:?}", task.resolved_name());

        let handle;
        {
            let mut context = task.context().borrow_mut();
            if context.is_registered() {
                error!("Task {:?} already registered", task.resolved_name());
                let err = format!("The task {:?} is already registered", task.resolved_name());
                return Err(Error::new(ErrorKind::InvalidArgument, err));
            }

            // register the handle and data internally.
            handle = self.allocate_handle()?;

            // SAFETY: As the implementation of the runtime we are allowed to freely modify the task
            // as by this point we already own it.
            let entry_func = context.take_entry_function();
            let data = ObjBox::new(ContextData::new(entry_func));
            context.register(handle, Some(ObjBox::coerce_obj(data)));
        }

        // SAFETY: We assert that this method is called only with valid tasks.
        let task = AssertValidTask::from_raw(task);

        // clear the task.
        // SAFETY: See above.
        let mut context = task.context().borrow_mut();
        context.set_run_status(TaskRunStatus::Idle);
        context.set_schedule_status(TaskScheduleStatus::Processing);
        context.take_panic_data();

        // `wait_task_on` requires a borrow of the context
        drop(context);

        // wait on all dependencies
        for dep in wait_on {
            if let Some(dep) = self.tasks.get(dep) {
                let dep = dep.clone();
                if let Err(e) = self.wait_task_on(task.clone(), dep) {
                    error!("Aborting registration, error: {}", e);
                    let mut context = task.context().borrow_mut();
                    let (handle, _) = context.unregister();

                    // SAFETY: The handle wasn't leaked to the outside world so it is safe
                    // to be reused.
                    self.free_handle_reuse(handle);
                    return Err(e);
                }
            }
        }

        let mut context = task.context().borrow_mut();

        // SAFETY: See above.
        let request = context.clear_request();

        match request {
            StatusRequest::None => {
                let data = context.scheduler_data();
                let private = data.private_data();
                if private.dependencies.is_empty() {
                    trace!(
                        "Registered task {:?} with id {} as runnable",
                        task.resolved_name(),
                        context.handle()
                    );

                    // SAFETY: The rest of the runtime wasn't informed of the task, so we
                    // are allowed to set an initial status.
                    context.set_schedule_status(TaskScheduleStatus::Runnable);

                    // `enqueue` will borrow the private context mutably, so we must relinquish our
                    // borrow to prevent a panic.
                    drop(private);
                    drop(context);

                    self.enqueue(task.clone());
                } else {
                    trace!(
                        "Registered task {:?} with id {} as waiting",
                        task.resolved_name(),
                        context.handle()
                    );

                    // SAFETY: The rest of the runtime wasn't informed of the task, so we
                    // are allowed to set an initial status.
                    context.set_schedule_status(TaskScheduleStatus::Waiting);

                    // makes the borrow checker happy.
                    drop(private);
                    drop(context);
                }
            }
            StatusRequest::Block => {
                trace!(
                    "Registered task {:?} with id {} as blocked",
                    task.resolved_name(),
                    context.handle()
                );

                // SAFETY: The rest of the runtime wasn't informed of the task, so we
                // are allowed to set an initial status.
                context.set_schedule_status(TaskScheduleStatus::Blocked);

                // makes the borrow checker happy.
                drop(context);
            }
            StatusRequest::Abort => {
                error!(
                    "Tries to register the task {:?} as aborted",
                    task.resolved_name()
                );
                let err = format!(
                    "A task may not request an abort upon registration, name {:?}",
                    task.resolved_name()
                );

                // Having a task aborted before registration is nonsensical,
                // so we can simply invalidate it and reuse it's handle.
                let (handle, _) = context.unregister();
                self.free_handle_reuse(handle);
                return Err(Error::new(ErrorKind::InvalidArgument, err));
            }
        }

        // register the task to the runtime.
        self.tasks.insert(handle, task);

        Ok(())
    }

    /// # Safety
    ///
    /// See [`unregister_task`](fimo_tasks_int::runtime::IScheduler::unregister_task)
    pub unsafe fn unregister_task(&mut self, task: AssertValidTask) -> Result<(), Error> {
        let mut context = task.context().borrow_mut();

        trace!("Unregistering task {}", context.handle());
        debug!("Task run status: {:?}", context.run_status());
        debug!("Task schedule status: {:?}", context.schedule_status());
        debug!("Task data: {:?}", context.scheduler_data());

        if context.run_status() != TaskRunStatus::Completed {
            error!("Task {} has not been completed", context.handle());
            let err = format!("Task {} has not been completed", context.handle());
            return Err(Error::new(ErrorKind::InvalidArgument, err));
        }

        // the task has been completed, we only need to unregister it and free the handle.
        let (handle, data) = context.unregister();
        let private = data.private_data();

        assert!(matches!(self.tasks.remove(&handle), Some(_)));
        debug_assert!(private.dependencies.is_empty());
        debug_assert!(private.waiters.is_empty());

        self.free_handle(handle);
        Ok(())
    }

    /// # Safety
    ///
    /// See [`wait_task_on`](fimo_tasks_int::runtime::IScheduler::wait_task_on)
    pub unsafe fn wait_task_on(
        &mut self,
        task: AssertValidTask,
        wait_on: AssertValidTask,
    ) -> Result<(), Error> {
        if task == wait_on {
            error!(
                "Task {} waiting on itself",
                task.context().borrow().handle()
            );
            let err = format!(
                "A task may not wait on itself, handle: {}",
                task.context().borrow().handle()
            );
            return Err(Error::new(ErrorKind::InvalidArgument, err));
        }

        let context = task.context().borrow();
        let wait_on_context = wait_on.context().borrow();

        let scheduler_data = context.scheduler_data();
        let wait_on_scheduler_data = wait_on_context.scheduler_data();

        trace!(
            "Setting task {} to wait for task {}",
            context.handle(),
            wait_on_context.handle()
        );
        debug!("Task run status: {:?}", context.run_status());
        debug!("Task schedule status: {:?}", context.schedule_status());
        debug!("Task data: {:?}", context.scheduler_data());

        let mut private = scheduler_data.private_data_mut();
        let mut wait_on_private = wait_on_scheduler_data.private_data_mut();

        // check that the task has not been completed.
        if context.run_status() == TaskRunStatus::Completed {
            error!("Can not wait, task {} already completed", context.handle());
            let err = format!("The task {} has already been completed", context.handle());
            return Err(Error::new(ErrorKind::InvalidArgument, err));
        }

        // skip if the dependency has already been completed.
        if wait_on_context.run_status() == TaskRunStatus::Completed {
            trace!(
                "Skipping wait for task {}, task {} already completed",
                context.handle(),
                wait_on_context.handle()
            );
            return Ok(());
        }

        // a task may not wait on another task multiple times.
        if private.dependencies.contains(&wait_on) {
            error!(
                "Task {} waiting on {} multiple times",
                context.handle(),
                context.handle()
            );
            let err = format!(
                "The task {} is already waiting on {}",
                context.handle(),
                wait_on_context.handle()
            );
            return Err(Error::new(ErrorKind::InvalidArgument, err));
        }

        // register the dependency
        private.dependencies.insert(wait_on.clone());
        wait_on_private.waiters.push(Reverse(task.clone()));

        // This method accepts arbitrary tasks, so it is possible that the task
        // was already inserted into the queue. In that case we simply mark it
        // as `Waiting` and let the scheduling logic handle the rest.
        //
        // In the future we may disallow this entirely by allowing only the own
        // task to wait on an arbitrary task.
        if context.schedule_status() == TaskScheduleStatus::Runnable {
            trace!("Set task {} to waiting", context.handle());

            // SAFETY: We know that only the runtime is allowed to modify the status
            // of a task. By that logic we can assume that status won't change unless
            // we are the ones changing it.
            context.set_schedule_status(TaskScheduleStatus::Waiting)
        }

        Ok(())
    }

    /// # Safety
    ///
    /// See [`notify_one`](fimo_tasks_int::runtime::IScheduler::notify_one)
    pub unsafe fn notify_one(&mut self, task: AssertValidTask) -> Result<Option<usize>, Error> {
        let context = task.context().borrow();
        let scheduler_data = context.scheduler_data();

        trace!("Notifying one waiter of task {}", context.handle());
        debug!("Task run status: {:?}", context.run_status());
        debug!("Task schedule status: {:?}", context.schedule_status());
        debug!("Task data: {:?}", scheduler_data);

        let mut private = scheduler_data.private_data_mut();

        // The actual logic of waking a task is implemented in the `notify_waiter`
        // method. We must simply select a suitable waiter. This is done by removing
        // the first waiter from the `waiters` heap, which returns the waiter with the
        // highest priority.
        if let Some(Reverse(waiter)) = private.waiters.pop() {
            self.notify_waiter(task.clone(), waiter);
            Ok(Some(private.waiters.len()))
        } else {
            trace!("No waiters, skipping");
            Ok(None)
        }
    }

    /// # Safety
    ///
    /// See [`notify_all`](fimo_tasks_int::runtime::IScheduler::notify_all)
    pub unsafe fn notify_all(&mut self, task: AssertValidTask) -> Result<usize, Error> {
        let context = task.context().borrow();
        let scheduler_data = context.scheduler_data();

        trace!("Notifying all waiters of task {}", context.handle());
        debug!("Task run status: {:?}", context.run_status());
        debug!("Task schedule status: {:?}", context.schedule_status());
        debug!("Task data: {:?}", context.scheduler_data());

        let mut private = scheduler_data.private_data_mut();

        let mut waiters = std::mem::take(&mut private.waiters);
        let num_waiters = waiters.len();

        // The actual logic of waking a task is implemented in the `notify_waiter`
        // method. We simply call that method with every waiter in the heap.
        while let Some(Reverse(waiter)) = waiters.pop() {
            self.notify_waiter(task.clone(), waiter)
        }

        Ok(num_waiters)
    }

    /// # Safety
    ///
    /// May only be called by [`notify_one`](#method.notify_one)
    /// and [`notify_all`](#method.notify_all).
    pub unsafe fn notify_waiter(&mut self, task: AssertValidTask, waiter: AssertValidTask) {
        let task_context = task.context().borrow();
        let waiter_context = waiter.context().borrow();
        let waiter_data = waiter_context.scheduler_data();

        trace!(
            "Notifying waiter {} that {} finished",
            waiter_context.handle(),
            task_context.handle()
        );
        debug!("Waiter run status: {:?}", waiter_context.run_status());
        debug!(
            "Waiter schedule status: {:?}",
            waiter_context.schedule_status()
        );
        debug!("Task data: {:?}", waiter_context.scheduler_data());

        let mut waiter_private = waiter_data.private_data_mut();
        assert!(waiter_private.dependencies.remove(&task));

        // make the task runnable if nothing prevents it.
        let schedule_status = waiter_context.schedule_status();
        if waiter_private.dependencies.is_empty() && schedule_status == TaskScheduleStatus::Waiting
        {
            trace!("Waking up task {}", waiter_context.handle());
            waiter_context.set_schedule_status(TaskScheduleStatus::Runnable);
            drop(waiter_private);
            drop(waiter_context);
            self.enqueue(waiter);
        }
    }

    /// # Safety
    ///
    /// See [`unblock_task`](fimo_tasks_int::runtime::IScheduler::unblock_task)
    pub unsafe fn unblock_task(&mut self, task: AssertValidTask) -> Result<(), Error> {
        let context = task.context().borrow();
        let scheduler_data = context.scheduler_data();
        let private = scheduler_data.private_data();

        trace!("Unblocking task {}", context.handle());
        debug!("Task run status: {:?}", context.run_status());
        debug!("Task schedule status: {:?}", context.schedule_status());
        debug!("Task data: {:?}", context.scheduler_data());

        // The status of a task may only be changed by the runtime, which
        // we have unique access to. So we can assume that they won't change
        // sporadically. In case the task is not blocked a runtime may decide
        // to simply do nothing. On the otherhand this may signal a logic error
        // from the part of a caller, so we decide to make it explicit by
        // returning an error.
        if context.schedule_status() != TaskScheduleStatus::Blocked {
            error!(
                "Invalid status for task {}: {:?}",
                context.handle(),
                context.schedule_status()
            );
            let err = format!(
                "Task {} is not blocked, status: {:?}",
                context.handle(),
                context.schedule_status()
            );
            return Err(Error::new(ErrorKind::InvalidArgument, err));
        }

        // Once unblocked we must decide if the task is runnable or if it has
        // other dependencies. If `dependencies` is empty, we know that nothing
        // is preventing the task from running and we simply enqueue it for further
        // processing.
        if private.dependencies.is_empty() {
            trace!("Marking task {} as runnable", context.handle());
            context.set_schedule_status(TaskScheduleStatus::Runnable);

            drop(private);
            drop(context);
            self.enqueue(task);
        } else {
            trace!("Marking task {} as waiting", context.handle());
            context.set_schedule_status(TaskScheduleStatus::Waiting)
        }

        Ok(())
    }
}

pub(crate) struct Msg<'a> {
    pub task: AssertValidTask,
    pub data: MsgData<'a>,
}

#[derive(Debug)]
pub(crate) enum MsgData<'a> {
    Completed {
        aborted: bool,
    },
    #[allow(clippy::type_complexity)]
    Yield {
        f: RawFfiFn<
            dyn FnOnce(&mut DynObj<dyn IScheduler + '_>, &DynObj<dyn IRawTask + '_>) + Send + 'a,
        >,
    },
}

impl MsgData<'_> {
    #[inline]
    pub fn msg_type(&self) -> &str {
        match &self {
            MsgData::Completed { .. } => "Completed",
            MsgData::Yield { .. } => "Yield",
        }
    }
}

#[repr(transparent)]
#[derive(Clone)]
pub(crate) struct AssertValidTask(&'static DynObj<dyn IRawTask + 'static>);

impl AssertValidTask {
    /// Constructs a `AssertValidTask` from an [`IRawTask`].
    ///
    /// # Safety
    ///
    /// The caller must ensure that the task is registered
    /// with the current runtime.
    #[inline]
    pub unsafe fn from_raw(task: &DynObj<dyn IRawTask + '_>) -> Self {
        let task = std::mem::transmute(task);
        Self(task)
    }

    /// Extracts the contained [`IRawTask`].
    #[inline]
    pub fn as_raw<'t>(&self) -> &DynObj<dyn IRawTask + 't> {
        self.0
    }

    /// Shorthand for `self.name().unwrap_or("unnamed")`.
    #[inline]
    pub fn name(&self) -> Option<&str> {
        self.0.name()
    }

    /// Shorthand for `self.name().unwrap_or("unnamed")`.
    #[inline]
    pub fn resolved_name(&self) -> &str {
        self.0.resolved_name()
    }

    /// Extracts the starting priority of the task.
    #[inline]
    pub fn priority(&self) -> TaskPriority {
        self.0.priority()
    }

    /// Returns a reference to the context.
    #[inline]
    pub fn context(&self) -> &AtomicRefCell<SchedulerContext<'_>> {
        let context = self.0.context();
        // SAFETY: SchedulerContext has a  transparent repr so it should be safe
        unsafe { std::mem::transmute(context) }
    }

    #[inline]
    pub fn context_atomic(&self) -> AtomicISchedulerContext<'_> {
        self.0.context_atomic()
    }
}

impl PartialEq for AssertValidTask {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // SAFETY: The invariant was checked at construction time.
        unsafe {
            self.context_atomic().handle().assume_init()
                == other.context_atomic().handle().assume_init()
        }
    }
}

impl PartialOrd for AssertValidTask {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Eq for AssertValidTask {}

impl Ord for AssertValidTask {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.priority().cmp(&other.priority())
    }
}

impl Debug for AssertValidTask {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("AssertValidTask")
            .field(&self.name())
            .field(&self.priority())
            .field(&self.context_atomic())
            .finish()
    }
}

#[repr(transparent)]
pub(crate) struct SchedulerContext<'a>(DynObj<dyn ISchedulerContext + 'a>);

impl<'a> SchedulerContext<'a> {
    /// Extracts the handle to the task.
    #[inline]
    pub fn handle(&self) -> TaskHandle {
        debug_assert!(self.is_registered());

        // SAFETY: Being registered is an invariant of an `SchedulerContext`.
        // Every registered task has a valid handle.
        unsafe { self.0.handle().assume_init() }
    }

    /// Checks whether the context has been marked as registered.
    #[inline]
    pub fn is_registered(&self) -> bool {
        self.0.is_registered()
    }

    /// Marks the context as unregistered.
    ///
    /// # Panics
    ///
    /// May panic if the task is not registered.
    #[inline]
    fn unregister(&mut self) -> (TaskHandle, ObjBox<ContextData>) {
        // SAFETY: Can only be called from a scheduler.
        let (handle, data) = unsafe { self.0.unregister() };
        let data = data.expect("Scheduler data taken from registered task");
        let data = ObjBox::downcast(data).expect("Invalid scheduler data");
        (handle, data)
    }

    /// Extracts the resume time.
    #[inline]
    pub fn resume_time(&self) -> SystemTime {
        self.0.resume_time()
    }

    /// Extracts the assigned worker.
    #[inline]
    pub fn worker(&self) -> Option<WorkerId> {
        self.0.worker()
    }

    /// Sets a new worker.
    ///
    /// Passing in `None` will automatically select an appropriate worker.
    ///
    /// # Note
    ///
    /// Must be implemented atomically.
    ///
    /// # Safety
    ///
    /// Behavior is undefined if any of the following conditions are violated:
    ///
    /// * A worker associated with the provided [`WorkerId`] does not exist.
    /// * The task has yielded it's execution and has cached thread-local variables.
    /// * Is used by someone other than the runtime implementation and the task is registered.
    #[inline]
    pub unsafe fn set_worker(&self, worker: Option<WorkerId>) {
        self.0.set_worker(worker)
    }

    /// Clears the requests and returns it.
    #[inline]
    pub unsafe fn clear_request(&self) -> StatusRequest {
        self.0.clear_request()
    }

    /// Extracts the current run status.
    #[inline]
    pub fn run_status(&self) -> TaskRunStatus {
        self.0.run_status()
    }

    /// Sets a new run status.
    #[inline]
    pub(super) fn set_run_status(&self, status: TaskRunStatus) {
        // SAFETY: Can only be called from a scheduler.
        unsafe { self.0.set_run_status(status) }
    }

    /// Extracts the current schedule status.
    #[inline]
    pub fn schedule_status(&self) -> TaskScheduleStatus {
        self.0.schedule_status()
    }

    /// Sets a new schedule status.
    ///
    /// # Safety
    ///
    /// Behavior is undefined if not called from a task scheduler.
    #[inline]
    pub unsafe fn set_schedule_status(&self, status: TaskScheduleStatus) {
        self.0.set_schedule_status(status)
    }

    /// Checks whether the task is empty.
    ///
    /// # Note
    ///
    /// May change after the task is registered with a runtime.
    #[inline]
    pub fn is_empty_task(&self) -> bool {
        self.0.is_empty_task()
    }

    /// Checks whether the task is panicking.
    #[inline]
    pub fn is_panicking(&self) -> bool {
        self.0.is_panicking()
    }

    /// Sets the panicking flag.
    ///
    /// # Panics
    ///
    /// May panic if the flag is already set.
    ///
    /// # Safety
    ///
    /// Behavior is undefined if not called from a task scheduler.
    #[inline]
    pub(super) fn set_panic(&mut self, panic: Option<ObjBox<PanicData>>) {
        let panic = panic.map(|p| {
            let p: ObjBox<DynObj<dyn IRustPanicData + Send>> = ObjBox::coerce_obj(p);
            ObjBox::cast_super(p)
        });

        // SAFETY: We are part of the scheduler.
        unsafe { self.0.set_panic(panic) }
    }

    /// Takes the panic data from the task.
    ///
    /// # Panics
    ///
    /// May panic if the task is registered.
    ///
    /// # Safety
    ///
    /// Behavior is undefined if the task has not completed or aborted it's execution.
    #[inline]
    unsafe fn take_panic_data(&mut self) -> Option<ObjBox<PanicData>> {
        self.0
            .take_panic_data()
            .map(|p| ObjBox::downcast(p).expect("Invalid panic data"))
    }

    /// Calls the cleanup function.
    #[inline]
    pub fn cleanup(&mut self) {
        self.0.cleanup()
    }

    /// Fetches a reference to the scheduler data.
    #[inline]
    pub fn scheduler_data(&self) -> &ContextData {
        self.0
            .scheduler_data()
            .expect("Invalid scheduler data")
            .downcast()
            .expect("Invalid scheduler data")
    }
}

#[derive(Debug, ObjectId)]
#[fetch_vtable(uuid = "c68fe659-beef-4341-9b75-f54b0ef387ff")]
pub(crate) struct ContextData {
    shared: AtomicRefCell<SharedContext>,
    private: AtomicRefCell<PrivateContext>,
}

/// Data used by the Scheduler and worker pool.
pub(crate) struct SharedContext {
    context: Option<Context>,
    panic: Option<ObjBox<PanicData>>,
    entry_func: Option<FfiFn<'static, dyn FnOnce() + Send + 'static>>,
}

unsafe impl Sync for SharedContext {}

/// Data used only by the Scheduler.
///
///
#[derive(Debug)]
pub(super) struct PrivateContext {
    in_queue: bool,
    processing: bool,
    /// Slot a task was assigned to.
    pub slot: Option<TaskSlot>,
    /// Dependencies on which the task must wait for.
    pub dependencies: BTreeSet<AssertValidTask>,
    /// Heap of tasks waiting on this task to finish,
    /// sorted by descending priority.
    pub waiters: BinaryHeap<Reverse<AssertValidTask>>,
}

impl ContextData {
    #[inline]
    fn new(f: Option<FfiFn<'_, dyn FnOnce() + Send + '_>>) -> Self {
        Self {
            shared: AtomicRefCell::new(SharedContext::new(f)),
            private: AtomicRefCell::new(PrivateContext::new()),
        }
    }

    /// Borrows the shared portion of the context mutably.
    #[inline]
    pub fn shared_data_mut(&self) -> AtomicRefMut<'_, SharedContext> {
        self.shared.borrow_mut()
    }

    /// Borrows the private portion of the context.
    #[inline]
    pub(super) fn private_data(&self) -> AtomicRef<'_, PrivateContext> {
        self.private.borrow()
    }

    /// Borrows the private portion of the context mutably.
    #[inline]
    pub(super) fn private_data_mut(&self) -> AtomicRefMut<'_, PrivateContext> {
        self.private.borrow_mut()
    }
}

impl SharedContext {
    #[inline]
    fn new(f: Option<FfiFn<'_, dyn FnOnce() + Send + '_>>) -> Self {
        Self {
            context: None,
            panic: None,
            // SAFETY: Ideally we would like to have a way to specify the concept of a
            // minimal lifetime. As that is currently not possible, we choose the
            // `'static` lifetime as a placeholder. As long as we ensure that the
            // task outlives the function it should be sound.
            entry_func: unsafe { std::mem::transmute(f) },
        }
    }

    #[inline]
    pub fn is_empty_context(&self) -> bool {
        self.context.is_none()
    }

    #[inline]
    pub fn take_context(&mut self) -> Option<Context> {
        self.context.take()
    }

    #[inline]
    pub fn set_context(&mut self, c: Context) {
        self.context = Some(c)
    }

    #[inline]
    pub fn take_panic(&mut self) -> Option<ObjBox<PanicData>> {
        self.panic.take()
    }

    #[inline]
    pub fn set_panic(&mut self, panic: ObjBox<PanicData>) {
        self.panic = Some(panic)
    }

    #[inline]
    pub fn take_entry_func(&mut self) -> Option<FfiFn<'static, dyn FnOnce() + Send + 'static>> {
        self.entry_func.take()
    }
}

impl PrivateContext {
    #[inline]
    fn new() -> Self {
        Self {
            in_queue: false,
            processing: false,
            slot: None,
            dependencies: Default::default(),
            waiters: Default::default(),
        }
    }

    /// Indicates whether the task is being processed.
    #[inline]
    pub fn is_processing(&self) -> bool {
        self.processing
    }

    /// Sets the processing flag to `p`.
    ///
    /// # Safety
    ///
    /// May only be used by the [`process_msg`](super::TaskScheduler::process_msg)
    /// function before and after processing the message.
    #[inline]
    pub unsafe fn toggle_processing(&mut self, p: bool) {
        debug_assert_ne!(self.processing, p);
        self.processing = p;
    }

    /// Indicates whether the task is already in the task queue.
    #[inline]
    pub fn is_in_queue(&self) -> bool {
        self.in_queue
    }

    /// Indicates that the task is present in the task queue.
    ///
    /// # Safety
    ///
    /// The task must be in the task queue.
    #[inline]
    unsafe fn assert_in_queue(&mut self) {
        self.in_queue = true;
    }

    /// Indicates that the task is not present in the task queue.
    ///
    /// # Safety
    ///
    /// The task must not be in the task queue.
    #[inline]
    pub unsafe fn assert_not_in_queue(&mut self) {
        debug_assert!(self.in_queue);
        self.in_queue = false;
    }
}

impl Debug for SharedContext {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SharedContext")
            .field("context", &self.context)
            .finish_non_exhaustive()
    }
}

#[derive(ObjectId)]
#[fetch_vtable(
    uuid = "d2e5a6f3-d5a0-41f0-a6b1-62d543c5c46b",
    interfaces(IRustPanicData)
)]
pub(crate) struct PanicData {
    data: Option<Box<dyn Any + Send + 'static>>,
}

impl PanicData {
    #[inline]
    pub fn new(e: Box<dyn Any + Send + 'static>) -> ObjBox<Self> {
        ObjBox::new(Self { data: Some(e) })
    }
}

impl IRustPanicData for PanicData {
    #[inline]
    unsafe fn take_rust_panic_impl(&mut self) -> Box<dyn Any + Send + 'static> {
        // safety: the function is called only once
        self.data.take().unwrap_unchecked()
    }
}