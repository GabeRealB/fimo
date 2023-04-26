//! Implementation of the task datastructure and interface.
use std::borrow::Cow;
use std::cell::UnsafeCell;
use std::sync::atomic::AtomicPtr;

use fimo_ffi::marshal::CTypeBridge;
use fimo_ffi::ptr::IBase;
use fimo_ffi::{interface, ConstStr, DynObj, FfiFn, Object};

use crate::blockable::{BlockList, IBlockable};
use crate::runtime2::IRuntime;

/// Result of a poll operation.
#[repr(i32)]
#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, PartialEq, Eq, CTypeBridge)]
pub enum PollResult {
    /// Represents that the operation has not been completed yet.
    Pending = 0,
    /// The operation has been completed.
    Completed = 1,
}

/// Location in a file.
#[repr(C)]
#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, CTypeBridge)]
pub struct Location<'a> {
    file: ConstStr<'a>,
    line: u32,
    col: u32,
}

impl<'a> Location<'a> {
    /// Returns the source location of the caller of this function.
    #[must_use]
    #[track_caller]
    pub fn caller() -> Location<'static> {
        let l = std::panic::Location::caller();
        Location::from_std(l)
    }

    /// Constructs a location from a [`std::panic::Location`].
    #[must_use]
    pub fn from_std(loc: &'a std::panic::Location<'a>) -> Location<'a> {
        Location {
            file: loc.file().into(),
            line: loc.line(),
            col: loc.column(),
        }
    }

    /// Returns the file from which the panic originated.
    #[must_use]
    pub fn file(&self) -> &str {
        self.file.into()
    }

    /// Returns the line from which the panic originated.
    #[must_use]
    pub fn line(&self) -> u32 {
        self.line
    }

    /// Returns the column from which the panic originated.
    #[must_use]
    pub fn column(&self) -> u32 {
        self.col
    }
}

interface! {
    #![interface_cfg(
        abi(explicit(abi = "C-unwind")),
        uuid = "64d5fbd8-c560-4792-a15b-7cfc0aa1ac44",
    )]

    /// Interface of a task.
    pub interface ITask: marker IBase + marker Sync {
        /// Returns the optional name of the task.
        fn name(&self) -> Option<&str>;

        /// Shorthand for `self.name().unwrap_or("unnamed")`.
        #[inline]
        #[interface_cfg(mapping = "exclude")]
        fn resolved_name(&self) -> &str {
            self.name().unwrap_or("unnamed")
        }

        /// Returns the spawn location of the task.
        fn spawn_location(&self) -> Option<Location<'static>>;

        /// Sets the local data of the task.
        fn local_data(&self) -> *mut ();

        /// Fetches a pointer to the registered local data.
        fn set_local_data(&self, local_data: *mut ());

        /// Returns a pointer to the block list.
        ///
        /// The pointer can be dereferenced, if the caller can
        /// guarantee that there are no other mutable references
        /// to the same object.
        fn block_list(&self) -> *mut DynObj<dyn IBlockable>;

        /// Polls the task.
        ///
        /// Returns a [`PollResult`], indicating whether the task
        /// has been completed, or needs to be polled again.
        ///
        /// # Safety
        ///
        /// It is unsound to call this function, if it is currently
        /// being called, or if the last call returned
        /// [`PollResult::Completed`].
        unsafe fn poll(&self, runtime: &'_ DynObj<dyn IRuntime + '_>) -> PollResult;
    }
}

/// Implementation of a task.
#[derive(Debug, Object)]
pub struct Task<'a> {
    local_data: AtomicPtr<()>,
    name: Option<Cow<'static, str>>,
    spawn_location: Option<&'static std::panic::Location<'static>>,
    block_list: UnsafeCell<BlockList>,
    poll_fn: UnsafeCell<FfiFn<'a, PollFnType<'a>>>,
}

/// Type of the poll function.
pub type PollFnType<'a> = dyn FnMut(&'_ DynObj<dyn IRuntime + '_>) -> PollResult + Sync + 'a;

unsafe impl<'a> Sync for Task<'a>
where
    FfiFn<'a, dyn FnMut(()) -> PollResult + Sync + 'a>: Sync,
    BlockList: Sync,
{
}

impl ITask for Task<'_> {
    fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    fn spawn_location(&self) -> Option<Location<'static>> {
        self.spawn_location.map(Location::from_std)
    }

    fn local_data(&self) -> *mut () {
        self.local_data.load(std::sync::atomic::Ordering::Acquire)
    }

    fn set_local_data(&self, local_data: *mut ()) {
        self.local_data
            .store(local_data, std::sync::atomic::Ordering::Release);
    }

    fn block_list(&self) -> *mut DynObj<dyn IBlockable> {
        fimo_ffi::ptr::coerce_obj_mut_raw(self.block_list.get())
    }

    unsafe fn poll(&self, runtime: &'_ DynObj<dyn IRuntime + '_>) -> PollResult {
        let poll_fn = &mut *self.poll_fn.get();
        poll_fn(runtime)
    }
}

/// A task builder.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Builder {
    name: Option<Cow<'static, str>>,
    spawn_location: &'static std::panic::Location<'static>,
}

impl Builder {
    /// Constructs a new `Builder`.
    #[track_caller]
    pub fn new() -> Self {
        Self {
            name: None,
            spawn_location: std::panic::Location::caller(),
        }
    }

    /// Names the task.
    pub fn with_name(mut self, name: Cow<'static, str>) -> Self {
        self.name = Some(name);
        self
    }

    /// Extends the name by appending a string.
    pub fn append_to_name(mut self, args: std::fmt::Arguments<'_>) -> Self {
        if let Some(name) = &mut self.name {
            let name = name.to_mut();
            *name = format!("{name}{args}");
        } else {
            self.name = Some(std::fmt::format(args).into());
        }

        self
    }

    /// Builds the [`Task`].
    ///
    /// # Safety
    ///
    /// The function must not panic.
    pub unsafe fn build<'a>(self, f: FfiFn<'a, PollFnType<'a>>) -> Task<'a> {
        Task {
            local_data: AtomicPtr::new(std::ptr::null_mut()),
            name: self.name,
            spawn_location: Some(self.spawn_location),
            poll_fn: UnsafeCell::new(f),
            block_list: Default::default(),
        }
    }
}

impl Default for Builder {
    #[track_caller]
    fn default() -> Self {
        Self::new()
    }
}
