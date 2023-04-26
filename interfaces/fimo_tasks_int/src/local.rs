//! Implementation of [`task_local!`].
//!
//! [`task_local!`]: crate::task_local

use std::{
    error::Error,
    fmt::{Debug, Display},
};

use crate::runtime2::{IRuntime, NotOwnedError};

/// A task local storage key which owns its contents.
///
/// It is instantiated with the [`task_local!`] macro and the primary method is
/// the [`with`] method.
///
/// The [`with`] method yields a reference to the contained value which cannot be
/// sent across tasks or escape the given closure.
///
/// # Initialization and Destruction
///
/// Initialization is dynamically performed on the first call to [`with`]
/// within a task, and values that implement [`Drop`] get destructed when a
/// task exits.
///
/// A `LocalKey`'s initializer cannot recursively depend on itself, and using
/// a `LocalKey` in this way will cause the initializer to infinitely recurse
/// on the first call to `with`.
///
/// [`with`]: LocalKey::with
/// [`task_local!`]: crate::task_local
pub struct LocalKey<T: 'static + Send> {
    #[allow(clippy::type_complexity)]
    inner: unsafe fn(
        Option<&mut Option<T>>,
        &(dyn IRuntime + '_),
    ) -> Result<&'static T, NotOwnedError>,
}

impl<T: 'static + Send> Debug for LocalKey<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LocalKey").finish_non_exhaustive()
    }
}

/// Declare a new task local storage key of type [`local::LocalKey`].
///
/// # Syntax
///
/// The macro wraps any number of static declarations and makes them task local.
/// Publicity and attributes for each static are allowed. Example:
///
/// ```
/// # use fimo_tasks_int::task_local;
/// use std::cell::RefCell;
/// task_local! {
///     pub static FOO: RefCell<u32> = RefCell::new(1);
///
///     #[allow(unused)]
///     static BAR: RefCell<f32> = RefCell::new(1.0);
/// }
/// # fn main() {}
/// ```
///
/// See [`LocalKey` documentation][`local::LocalKey`] for more
/// information.
///
/// [`local::LocalKey`]: crate::local::LocalKey
#[macro_export]
macro_rules! task_local {
    // empty (base case for the recursion)
    () => {};

    ($(#[$attr:meta])* $vis:vis static $name:ident: $t:ty = const { $init:expr }; $($rest:tt)*) => (
        $crate::__task_local_inner!($(#[$attr])* $vis $name, $t, const $init);
        $crate::task_local!($($rest)*);
    );

    ($(#[$attr:meta])* $vis:vis static $name:ident: $t:ty = const { $init:expr }) => (
        $crate::__task_local_inner!($(#[$attr])* $vis $name, $t, const $init);
    );

    // process multiple declarations
    ($(#[$attr:meta])* $vis:vis static $name:ident: $t:ty = $init:expr; $($rest:tt)*) => (
        $crate::__task_local_inner!($(#[$attr])* $vis $name, $t, $init);
        $crate::task_local!($($rest)*);
    );

    // handle a single declaration
    ($(#[$attr:meta])* $vis:vis static $name:ident: $t:ty = $init:expr) => (
        $crate::__task_local_inner!($(#[$attr])* $vis $name, $t, $init);
    );
}

#[doc(hidden)]
#[macro_export]
macro_rules! __task_local_inner {
    (@getit $t:ty) => {
        #[inline]
        #[deny(unsafe_op_in_unsafe_fn)]
        unsafe fn __getit(
            init: std::option::Option<&mut std::option::Option<$t>>,
            runtime: &(dyn $crate::runtime2::IRuntime + '_),
        ) -> std::result::Result<&'static $t, $crate::runtime2::NotOwnedError> {
            let key = __getit as usize as *const ();
            let ptr = unsafe {
                $crate::runtime2::Runtime::get_or_init_tls_key(
                    runtime,
                    key,
                    move || {
                        if let std::option::Option::Some(init) = init {
                            if let std::option::Option::Some(value) = init.take() {
                                return value;
                            } else if std::cfg!(debug_assertions) {
                                std::unreachable!("missing default value");
                            }
                        }

                        __init()
                    }
                )?
            };
            unsafe { std::result::Result::Ok(&*ptr) }
        }
    };

    // used to generate the `LocalKey` value for const-initialized task locals
    (@key $t:ty, const $init:expr) => {{
        const INIT_EXPR: $t = $init;

        #[inline]
        const fn __init() -> $t { INIT_EXPR }
        $crate::__task_local_inner!(@getit $t);

        unsafe {
            $crate::local::LocalKey::__new(__getit)
        }
    }};

    // used to generate the `LocalKey` value for `task_local!`
    (@key $t:ty, $init:expr) => {{
        #[inline]
        fn __init() -> $t { $init }
        $crate::__task_local_inner!(@getit $t);

        unsafe {
            $crate::local::LocalKey::__new(__getit)
        }
    }};
    ($(#[$attr:meta])* $vis:vis $name:ident, $t:ty, $($init:tt)*) => {
        $(#[$attr])* $vis const $name: $crate::local::LocalKey<$t> =
            $crate::__task_local_inner!(@key $t, $($init)*);
    }
}

/// An error returned by [`LocalKey::try_with`].
#[non_exhaustive]
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct AccessError;

impl Debug for AccessError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AccessError").finish()
    }
}

impl Display for AccessError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "not part of the runtime")
    }
}

impl Error for AccessError {}

impl<T: 'static + Send> LocalKey<T> {
    #[doc(hidden)]
    #[allow(clippy::type_complexity)]
    pub const unsafe fn __new(
        inner: unsafe fn(
            Option<&mut Option<T>>,
            &(dyn IRuntime + '_),
        ) -> Result<&'static T, NotOwnedError>,
    ) -> Self {
        Self { inner }
    }

    /// Acquires a reference to the value in this task-local storage key.
    ///
    /// This will lazily initialize the value if this task has not referenced
    /// this key yet.
    ///
    /// # Panics
    ///
    /// This function will panic if the caller is not owned by the runtime.
    pub fn with<R>(&'static self, r: &impl IRuntime, f: impl FnOnce(&T) -> R) -> R {
        self.try_with(r, f).expect(
            "cannot access a Task Local Storage value from a thread not owned by the runtime",
        )
    }

    /// Acquires a reference to the value in this task-local storage key.
    ///
    /// This will lazily initialize the value if this task has not referenced
    /// this key yet. If the caller is not part of the runtime, this function
    /// will return an [`AccessError`].
    pub fn try_with<R>(
        &'static self,
        r: &impl IRuntime,
        f: impl FnOnce(&T) -> R,
    ) -> Result<R, AccessError> {
        unsafe {
            let task_local = (self.inner)(None, r).map_err(|_| AccessError)?;
            Ok(f(task_local))
        }
    }
}
