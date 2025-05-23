//! Bindings to the fimo tasks symbols.
#![feature(allocator_api)]

use std::{marker::PhantomData, time::Duration};

use fimo_std::error::{AnyError, to_result, to_result_indirect_in_place};

pub mod bindings;
pub mod symbols;

mod command_buffer;
mod local;
mod task;
mod worker_group;

pub use command_buffer::*;
use fimo_std::{
    tracing::{Config, Level, ThreadAccess},
    utils::FFISharable,
};
pub use local::*;
pub use task::*;
pub use worker_group::*;

/// Context of runtime.
#[derive(Debug)]
#[repr(transparent)]
pub struct Context(bindings::FiTasksContext);

impl Context {
    /// Returns whether the current thread is a worker thread managed by some worker group of the
    /// context.
    ///
    /// Some operations can only be performed by worker threads.
    ///
    /// # Examples
    ///
    /// ```
    /// # fimo_tasks_meta::__private_with_context(|_module, context| {
    /// use fimo_tasks_meta::{CommandBuffer, TaskStatus, WorkerGroupBuilder};
    /// use std::num::NonZeroUsize;
    ///
    /// // Outside a worker group.
    /// assert_eq!(context.is_worker(), false);
    ///
    /// // Inside a worker group.
    /// let group = WorkerGroupBuilder::new(c"doctest", &[Default::default()], None)
    ///     .with_worker_count(NonZeroUsize::new(1))
    ///     .build(&context)
    ///     .expect("could not create worker group");
    ///
    /// let mut buffer = CommandBuffer::new();
    /// let task = buffer.spawn_task(|context| {
    ///     assert_eq!(context.is_worker(), true);
    /// });
    ///
    /// buffer
    ///     .block_on(&group)
    ///     .expect("could not enqueue command buffer");
    /// assert_eq!(task.completion_status(), Some(TaskStatus::Completed));
    /// # });
    /// ```
    pub fn is_worker(&self) -> bool {
        // Safety: FFI call is safe
        unsafe { (self.vtable().v0.is_worker.unwrap_unchecked())(self.data()) }
    }

    /// Returns the unique id of the current task.
    ///
    /// The id will be unique for as long as the task is being executed, but may be reused by other
    /// tasks upon completion.
    ///
    /// Can only be called successfully from a task.
    ///
    /// # Examples
    ///
    /// ```
    /// # fimo_tasks_meta::__private_with_context(|_module, context| {
    /// use fimo_tasks_meta::{CommandBuffer, TaskStatus, WorkerGroupBuilder};
    /// use std::num::NonZeroUsize;
    ///
    /// // Outside a worker group.
    /// assert!(context.task_id().is_err());
    ///
    /// // Inside a worker group.
    /// let group = WorkerGroupBuilder::new(c"doctest", &[Default::default()], None)
    ///     .with_worker_count(NonZeroUsize::new(1))
    ///     .build(&context)
    ///     .expect("could not create worker group");
    ///
    /// let mut buffer = CommandBuffer::new();
    /// let task = buffer.spawn_task(|context| {
    ///     assert!(context.task_id().is_ok());
    /// });
    ///
    /// buffer
    ///     .block_on(&group)
    ///     .expect("could not enqueue command buffer");
    /// assert_eq!(task.completion_status(), Some(TaskStatus::Completed));
    /// # });
    /// ```
    pub fn task_id(&self) -> Result<TaskId, AnyError> {
        // Safety: FFI call is safe
        let id = unsafe {
            to_result_indirect_in_place(|err, id| {
                *err = (self.vtable().v0.task_id.unwrap_unchecked())(self.data(), id.as_mut_ptr());
            })?
        };

        Ok(TaskId(id))
    }

    /// Returns the unique id of the current worker.
    ///
    /// Can only be called successfully from a task.
    ///
    /// # Examples
    ///
    /// ```
    /// # fimo_tasks_meta::__private_with_context(|_module, context| {
    /// use fimo_tasks_meta::{CommandBuffer, TaskStatus, WorkerGroupBuilder};
    /// use std::num::NonZeroUsize;
    ///
    /// // Outside a worker group.
    /// assert!(context.worker_id().is_err());
    ///
    /// // Inside a worker group.
    /// let group = WorkerGroupBuilder::new(c"doctest", &[Default::default()], None)
    ///     .with_worker_count(NonZeroUsize::new(1))
    ///     .build(&context)
    ///     .expect("could not create worker group");
    ///
    /// let mut buffer = CommandBuffer::new();
    /// let task = buffer.spawn_task(|context| {
    ///     assert!(context.worker_id().is_ok());
    /// });
    ///
    /// buffer
    ///     .block_on(&group)
    ///     .expect("could not enqueue command buffer");
    /// assert_eq!(task.completion_status(), Some(TaskStatus::Completed));
    /// # });
    /// ```
    pub fn worker_id(&self) -> Result<WorkerId, AnyError> {
        // Safety: FFI call is safe
        let id = unsafe {
            to_result_indirect_in_place(|err, id| {
                *err =
                    (self.vtable().v0.worker_id.unwrap_unchecked())(self.data(), id.as_mut_ptr());
            })?
        };

        Ok(WorkerId(id))
    }

    /// Returns a handle to the current [`WorkerGroup`].
    ///
    /// Can only be called successfully from a task.
    ///
    /// # Examples
    ///
    /// ```
    /// # fimo_tasks_meta::__private_with_context(|_module, context| {
    /// use fimo_tasks_meta::{CommandBuffer, TaskStatus, WorkerGroupBuilder};
    /// use std::num::NonZeroUsize;
    ///
    /// // Outside a worker group.
    /// assert!(context.worker_group().is_err());
    ///
    /// // Inside a worker group.
    /// let group = WorkerGroupBuilder::new(c"doctest", &[Default::default()], None)
    ///     .with_worker_count(NonZeroUsize::new(1))
    ///     .build(&context)
    ///     .expect("could not create worker group");
    /// let group_id = group.id();
    ///
    /// let mut buffer = CommandBuffer::new();
    /// let task = buffer.spawn_task(move |context| {
    ///     let group = context.worker_group().unwrap();
    ///     assert_eq!(group.id(), group_id);
    /// });
    ///
    /// buffer
    ///     .block_on(&group)
    ///     .expect("could not enqueue command buffer");
    /// assert_eq!(task.completion_status(), Some(TaskStatus::Completed));
    /// # });
    /// ```
    pub fn worker_group(&self) -> Result<WorkerGroup<'_>, AnyError> {
        // Safety: FFI call is safe
        let group = unsafe {
            to_result_indirect_in_place(|err, group| {
                *err = (self.vtable().v0.worker_group.unwrap_unchecked())(
                    self.data(),
                    group.as_mut_ptr(),
                );
            })?
        };

        Ok(WorkerGroup(group, PhantomData))
    }

    /// Acquires a handle to a [`WorkerGroup`] assigned to the identifier `id`.
    ///
    /// # Examples
    ///
    /// ```
    /// # fimo_tasks_meta::__private_with_context(|_module, context| {
    /// use fimo_tasks_meta::WorkerGroupBuilder;
    /// use std::num::NonZeroUsize;
    ///
    /// let group = WorkerGroupBuilder::new(c"doctest", &[Default::default()], None)
    ///     .with_worker_count(NonZeroUsize::new(1))
    ///     .build(&context)
    ///     .expect("could not create worker group");
    /// let group_id = group.id();
    ///
    /// let doctest_group = context
    ///     .worker_group_by_id(group_id)
    ///     .expect("could not find worker group");
    /// assert_eq!(group.id(), doctest_group.id());
    /// # });
    /// ```
    pub fn worker_group_by_id(&self, id: WorkerGroupId) -> Result<WorkerGroup<'_>, AnyError> {
        // Safety: FFI call is safe
        let group = unsafe {
            to_result_indirect_in_place(|err, group| {
                *err = (self.vtable().v0.worker_group_by_id.unwrap_unchecked())(
                    self.data(),
                    id.0,
                    group.as_mut_ptr(),
                );
            })?
        };

        Ok(WorkerGroup(group, PhantomData))
    }

    /// Queries a list of [`WorkerGroup`]s available in the context.
    ///
    /// # Examples
    ///
    /// ```
    /// # fimo_tasks_meta::__private_with_context(|_module, context| {
    /// use fimo_tasks_meta::WorkerGroupBuilder;
    /// use std::num::NonZeroUsize;
    ///
    /// let group = WorkerGroupBuilder::new(c"doctest", &[Default::default()], None)
    ///     .with_worker_count(NonZeroUsize::new(1))
    ///     .with_queryable(true)
    ///     .build(&context)
    ///     .expect("could not create worker group");
    /// let group_id = group.id();
    ///
    /// let query = context.query_worker_groups().unwrap();
    /// assert!(query.iter().any(|grp| grp.id() == group_id));
    /// # });
    /// ```
    pub fn query_worker_groups(&self) -> Result<WorkerGroupQuery<'_>, AnyError> {
        // Safety: FFI call is safe
        let query = unsafe {
            to_result_indirect_in_place(|err, query| {
                *err = (self.vtable().v0.query_worker_groups.unwrap_unchecked())(
                    self.data(),
                    query.as_mut_ptr(),
                );
            })?
        };

        Ok(WorkerGroupQuery { query, ctx: self })
    }

    /// Yields the execution of the current task back to the scheduler.
    ///
    /// Yielding a task may allow other tasks to be scheduled.
    ///
    /// Can only be called successfully from a task.
    ///
    /// # Examples
    ///
    /// ```
    /// # fimo_tasks_meta::__private_with_context(|_module, context| {
    /// use fimo_tasks_meta::{CommandBuffer, TaskStatus, WorkerGroupBuilder};
    /// use std::num::NonZeroUsize;
    ///
    /// // Outside a worker group.
    /// assert!(context.yield_now().is_err());
    ///
    /// // Inside a worker group.
    /// let group = WorkerGroupBuilder::new(c"doctest", &[Default::default()], None)
    ///     .with_worker_count(NonZeroUsize::new(1))
    ///     .build(&context)
    ///     .expect("could not create worker group");
    ///
    /// let mut buffer = CommandBuffer::new();
    /// let task = buffer.spawn_task(move |context| {
    ///     assert!(context.yield_now().is_ok());
    /// });
    ///
    /// buffer
    ///     .block_on(&group)
    ///     .expect("could not enqueue command buffer");
    /// assert_eq!(task.completion_status(), Some(TaskStatus::Completed));
    /// # });
    /// ```
    pub fn yield_now(&self) -> Result<(), AnyError> {
        // Safety: FFI call is safe
        unsafe { to_result((self.vtable().v0.yield_.unwrap_unchecked())(self.data())) }
    }

    /// Pauses the execution of the current task for the specified duration.
    ///
    /// The task may sleep longer than the duration specified. It will never sleep less.
    ///
    /// Can only be called successfully from a task.
    ///
    /// # Examples
    ///
    /// ```
    /// # fimo_tasks_meta::__private_with_context(|_module, context| {
    /// use fimo_tasks_meta::{CommandBuffer, TaskStatus, WorkerGroupBuilder};
    /// use std::{num::NonZeroUsize, time};
    ///
    /// let ten_millis = time::Duration::from_millis(10);
    ///
    /// // Outside a worker group.
    /// assert!(context.sleep(ten_millis).is_err());
    ///
    /// // Inside a worker group.
    /// let group = WorkerGroupBuilder::new(c"doctest", &[Default::default()], None)
    ///     .with_worker_count(NonZeroUsize::new(1))
    ///     .build(&context)
    ///     .expect("could not create worker group");
    ///
    /// let mut buffer = CommandBuffer::new();
    /// let task = buffer.spawn_task(move |context| {
    ///     let now = time::Instant::now();
    ///     context.sleep(ten_millis).unwrap();
    ///     assert!(now.elapsed() >= ten_millis);
    /// });
    ///
    /// buffer
    ///     .block_on(&group)
    ///     .expect("could not enqueue command buffer");
    /// assert_eq!(task.completion_status(), Some(TaskStatus::Completed));
    /// # });
    /// ```
    pub fn sleep(&self, duration: Duration) -> Result<(), AnyError> {
        let secs = duration.as_secs();
        let nanos = duration.subsec_nanos();
        let duration = fimo_std::time::Duration::new(secs, nanos);

        // Safety: FFI call is safe
        unsafe {
            to_result(self.vtable().v0.sleep.unwrap_unchecked()(
                self.data(),
                std::mem::transmute::<fimo_std::time::Duration, fimo_std::bindings::FimoDuration>(
                    duration,
                ),
            ))
        }
    }

    #[inline(always)]
    fn data(&self) -> *mut std::ffi::c_void {
        self.0.data
    }

    #[inline(always)]
    fn vtable(&self) -> &bindings::FiTasksVTable {
        // Safety: The VTable is always initialized
        unsafe { &*self.0.vtable }
    }
}

// Safety: Sound by invariant
unsafe impl Send for Context {}

// Safety: Sound by invariant
unsafe impl Sync for Context {}

impl FFISharable<bindings::FiTasksContext> for Context {
    type BorrowedView<'a> = std::convert::Infallible;

    fn share_to_ffi(&self) -> bindings::FiTasksContext {
        self.0
    }

    unsafe fn borrow_from_ffi<'a>(_ffi: bindings::FiTasksContext) -> Self::BorrowedView<'a> {
        unreachable!("can not borrow a ffi context")
    }
}

#[doc(hidden)]
pub fn __private_with_context(
    f: impl FnOnce(&fimo_std::module::instance::PseudoInstance, &Context),
) {
    use fimo_std::{
        r#async::{BlockingContext, EventLoop},
        context::ContextBuilder,
        module::{instance::GenericInstance, loading_set::LoadingSet, symbols::SymbolInfo},
        tracing::default_subscriber,
    };
    use std::path::PathBuf;

    let modules_dir = std::env::var("MODULES_DIR")
        .expect("MODULES_DIR environment variable is required while testing");
    let mut tasks_dir = PathBuf::from(modules_dir);
    tasks_dir.push("fimo_tasks_impl");
    tasks_dir.push("module.module");
    let tasks_dir = tasks_dir.into_os_string().into_string().unwrap();

    let context = ContextBuilder::new()
        .with_tracing_config(
            Config::default()
                .with_max_level(Level::Trace)
                .with_subscribers(&[default_subscriber()]),
        )
        .build()
        .expect("could not build fimo context");
    {
        let _access = ThreadAccess::new(&context);
        let _event_loop = EventLoop::new(&context).expect("could not create event loop");

        let blocking = BlockingContext::new(&context).expect("could not create blocking context");

        blocking.block_on(async {
            let set = LoadingSet::new(&context).unwrap();
            // Safety:
            unsafe {
                set.view()
                    .add_modules_from_path(&tasks_dir, |_| {
                        fimo_std::module::loading_set::FilterRequest::Load
                    })
                    .unwrap();
            }
            set.view().commit().await.unwrap();

            let instance = fimo_std::module::instance::PseudoInstance::new(&context)
                .expect("could not create pseudo module");
            let tasks_module =
                fimo_std::module::info::Info::find_by_name(&context, c"fimo_tasks_impl")
                    .expect("could not find the tasks module");

            instance
                .add_namespace(symbols::Context::NAMESPACE)
                .expect("could not include the tasks namespace");
            instance
                .add_dependency(&tasks_module)
                .expect("could not acquire the dependency to the tasks module");

            let context = instance
                .load_symbol::<symbols::Context>()
                .expect("could not load context symbol");

            f(&instance, &context);
        });
    }
    drop(context);
}
