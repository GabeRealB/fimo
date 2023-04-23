//! Marshalling utilities.
use std::ptr::NonNull;

pub use fimo_ffi_codegen::CTypeBridge;

/// Bridge for Rust to Rust types.
pub trait RustTypeBridge {
    /// Type to marshal to.
    type Type;

    /// Marshals the type.
    fn marshal(self) -> Self::Type;

    /// Demarshals the type.
    fn demarshal(x: Self::Type) -> Self;
}

impl<T> RustTypeBridge for T {
    type Type = Self;

    #[inline(always)]
    fn marshal(self) -> Self::Type {
        self
    }

    #[inline(always)]
    fn demarshal(x: Self::Type) -> Self {
        x
    }
}

/// Bridge for Rust to C types.
///
/// # Safety
///
/// Implementations must always implement the entire trait
/// without making use of the default implementations or use
/// all default implementations.
pub unsafe trait CTypeBridge {
    /// Type to marshal to.
    type Type;

    /// Marshals the type.
    fn marshal(self) -> Self::Type;

    /// Demarshals the type.
    ///
    /// # Safety
    ///
    /// The marshaling operation represents a non injective mapping
    /// from the type `T` to an arbitrary type `U`. Therefore it is likely,
    /// that multiple types are mapped to the same `U` type.
    ///
    /// When calling this method, one must ensure that the same marshaler
    /// is used for both marshalling and demarshalling, i. e. `T::marshal`
    /// followed by `T::demarshal`, or that the marshaler is able to work
    /// with the value one intends to demarshal.
    unsafe fn demarshal(x: Self::Type) -> Self;
}

macro_rules! identity_impls {
    ($($T:ident),+) => {
        $(
            unsafe impl CTypeBridge for $T {
                type Type = Self;

                #[inline(always)]
                fn marshal(self) -> Self::Type {
                    self
                }

                #[inline(always)]
                unsafe fn demarshal(x: Self::Type) -> Self {
                    x
                }
            }
        )+
    };
}

// Implement for the identity mapping for primitive whose layout
// matches the c layout.
identity_impls! {
    bool,
    f32,
    f64,
    i8,
    i16,
    i32,
    i64,
    isize,
    u8,
    u16,
    u32,
    u64,
    usize
}

// Implementation for primitive types whose layout differ.

/// C compatible [`i128`].
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, CTypeBridge)]
pub struct I128C {
    lower: u64,
    higher: u64,
}

/// C compatible [`u128`].
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, CTypeBridge)]
pub struct U128C {
    lower: u64,
    higher: u64,
}

unsafe impl CTypeBridge for i128 {
    type Type = I128C;

    fn marshal(self) -> Self::Type {
        unsafe { std::mem::transmute(self) }
    }

    unsafe fn demarshal(x: Self::Type) -> Self {
        std::mem::transmute(x)
    }
}

unsafe impl CTypeBridge for u128 {
    type Type = U128C;

    fn marshal(self) -> Self::Type {
        unsafe { std::mem::transmute(self) }
    }

    unsafe fn demarshal(x: Self::Type) -> Self {
        std::mem::transmute(x)
    }
}

unsafe impl CTypeBridge for char {
    type Type = u32;

    fn marshal(self) -> Self::Type {
        self as u32
    }

    unsafe fn demarshal(x: Self::Type) -> Self {
        Self::from_u32_unchecked(x)
    }
}

unsafe impl<T, const N: usize> CTypeBridge for [T; N]
where
    T: CTypeBridge,
{
    type Type = [T::Type; N];

    fn marshal(self) -> Self::Type {
        self.map(|x| x.marshal())
    }

    unsafe fn demarshal(x: Self::Type) -> Self {
        x.map(|x| T::demarshal(x))
    }
}

// Specialize for pointer types.
unsafe impl<T: ?Sized> CTypeBridge for *const T
where
    *const T: private::CPointerRep,
{
    default type Type = <*const T as private::CPointerRep>::T;

    #[inline]
    default fn marshal(self) -> Self::Type {
        let x = <*const T as private::CPointerRep>::split(self);
        let x = std::mem::ManuallyDrop::new(x);
        unsafe { std::mem::transmute_copy(&x) }
    }

    #[inline]
    default unsafe fn demarshal(x: Self::Type) -> Self {
        let x = std::mem::ManuallyDrop::new(x);
        let x: <*const T as private::CPointerRep>::T = std::mem::transmute_copy(&x);
        <*const T as private::CPointerRep>::reconstruct(x)
    }
}

unsafe impl<T: ?Sized> CTypeBridge for *mut T
where
    *mut T: private::CPointerRep,
{
    default type Type = <*mut T as private::CPointerRep>::T;

    #[inline]
    default fn marshal(self) -> Self::Type {
        let x = <*mut T as private::CPointerRep>::split(self);
        let x = std::mem::ManuallyDrop::new(x);
        unsafe { std::mem::transmute_copy(&x) }
    }

    #[inline]
    default unsafe fn demarshal(x: Self::Type) -> Self {
        let x = std::mem::ManuallyDrop::new(x);
        let x: <*mut T as private::CPointerRep>::T = std::mem::transmute_copy(&x);
        <*mut T as private::CPointerRep>::reconstruct(x)
    }
}

unsafe impl<T: ?Sized> CTypeBridge for NonNull<T>
where
    *mut T: CTypeBridge,
{
    type Type = <*mut T as CTypeBridge>::Type;

    fn marshal(self) -> Self::Type {
        <*mut T as CTypeBridge>::marshal(self.as_ptr())
    }

    unsafe fn demarshal(x: Self::Type) -> Self {
        let ptr = <*mut T as CTypeBridge>::demarshal(x);
        Self::new_unchecked(ptr)
    }
}

unsafe impl<'a, T: ?Sized> CTypeBridge for &'a T
where
    &'a T: private::CPointerRep,
{
    default type Type = <&'a T as private::CPointerRep>::T;

    #[inline]
    default fn marshal(self) -> Self::Type {
        let x = <&'a T as private::CPointerRep>::split(self);
        let x = std::mem::ManuallyDrop::new(x);
        unsafe { std::mem::transmute_copy(&x) }
    }

    #[inline]
    default unsafe fn demarshal(x: Self::Type) -> Self {
        let x = std::mem::ManuallyDrop::new(x);
        let x: <&'a T as private::CPointerRep>::T = std::mem::transmute_copy(&x);
        <&'a T as private::CPointerRep>::reconstruct(x)
    }
}

unsafe impl<'a, T: ?Sized> CTypeBridge for &'a mut T
where
    &'a mut T: private::CPointerRep,
{
    default type Type = <&'a mut T as private::CPointerRep>::T;

    #[inline]
    default fn marshal(self) -> Self::Type {
        let x = <&'a mut T as private::CPointerRep>::split(self);
        let x = std::mem::ManuallyDrop::new(x);
        unsafe { std::mem::transmute_copy(&x) }
    }

    #[inline]
    default unsafe fn demarshal(x: Self::Type) -> Self {
        let x = std::mem::ManuallyDrop::new(x);
        let x: <&'a mut T as private::CPointerRep>::T = std::mem::transmute_copy(&x);
        <&'a mut T as private::CPointerRep>::reconstruct(x)
    }
}

// Function pointers

macro_rules! fnptr_impls_safety_abi {
    ($FnTy: ty, $($Arg: ident),*) => {
        unsafe impl<Ret, $($Arg),*> CTypeBridge for $FnTy {
            type Type = Self;

            #[inline]
            fn marshal(self) -> Self::Type {
                self
            }

            #[inline]
            unsafe fn demarshal(x: Self::Type) -> Self {
                x
            }
        }
    }
}

macro_rules! fnptr_impls_args {
    ($($Arg: ident),+) => {
        fnptr_impls_safety_abi! { extern "Rust" fn($($Arg),+) -> Ret, $($Arg),+ }
        fnptr_impls_safety_abi! { extern "C" fn($($Arg),+) -> Ret, $($Arg),+ }
        fnptr_impls_safety_abi! { extern "C" fn($($Arg),+ , ...) -> Ret, $($Arg),+ }
        fnptr_impls_safety_abi! { extern "C-unwind" fn($($Arg),+) -> Ret, $($Arg),+ }
        fnptr_impls_safety_abi! { extern "C-unwind" fn($($Arg),+ , ...) -> Ret, $($Arg),+ }
        fnptr_impls_safety_abi! { unsafe extern "Rust" fn($($Arg),+) -> Ret, $($Arg),+ }
        fnptr_impls_safety_abi! { unsafe extern "C" fn($($Arg),+) -> Ret, $($Arg),+ }
        fnptr_impls_safety_abi! { unsafe extern "C" fn($($Arg),+ , ...) -> Ret, $($Arg),+ }
        fnptr_impls_safety_abi! { unsafe extern "C-unwind" fn($($Arg),+) -> Ret, $($Arg),+ }
        fnptr_impls_safety_abi! { unsafe extern "C-unwind" fn($($Arg),+ , ...) -> Ret, $($Arg),+ }
    };
    () => {
        // No variadic functions with 0 parameters
        fnptr_impls_safety_abi! { extern "Rust" fn() -> Ret, }
        fnptr_impls_safety_abi! { extern "C" fn() -> Ret, }
        fnptr_impls_safety_abi! { extern "C-unwind" fn() -> Ret, }
        fnptr_impls_safety_abi! { unsafe extern "Rust" fn() -> Ret, }
        fnptr_impls_safety_abi! { unsafe extern "C" fn() -> Ret, }
        fnptr_impls_safety_abi! { unsafe extern "C-unwind" fn() -> Ret, }
    };
}

fnptr_impls_args! {}
fnptr_impls_args! { T }
fnptr_impls_args! { A, B }
fnptr_impls_args! { A, B, C }
fnptr_impls_args! { A, B, C, D }
fnptr_impls_args! { A, B, C, D, E }
fnptr_impls_args! { A, B, C, D, E, F }
fnptr_impls_args! { A, B, C, D, E, F, G }
fnptr_impls_args! { A, B, C, D, E, F, G, H }
fnptr_impls_args! { A, B, C, D, E, F, G, H, I }
fnptr_impls_args! { A, B, C, D, E, F, G, H, I, J }
fnptr_impls_args! { A, B, C, D, E, F, G, H, I, J, K }
fnptr_impls_args! { A, B, C, D, E, F, G, H, I, J, K, L }

// Implement for wrappers
unsafe impl<T> CTypeBridge for std::mem::ManuallyDrop<T>
where
    T: CTypeBridge,
{
    type Type = std::mem::ManuallyDrop<T::Type>;

    fn marshal(self) -> Self::Type {
        let inner = std::mem::ManuallyDrop::into_inner(self);
        std::mem::ManuallyDrop::new(inner.marshal())
    }

    unsafe fn demarshal(x: Self::Type) -> Self {
        let inner = std::mem::ManuallyDrop::into_inner(x);
        std::mem::ManuallyDrop::new(T::demarshal(inner))
    }
}

unsafe impl<T> CTypeBridge for std::mem::MaybeUninit<T>
where
    T: CTypeBridge<Type = T>,
{
    type Type = Self;

    fn marshal(self) -> Self::Type {
        self
    }

    unsafe fn demarshal(x: Self::Type) -> Self {
        x
    }
}

mod private {
    use super::CTypeBridge;

    pub trait CPointerRep {
        type T;

        fn split(self) -> Self::T;

        unsafe fn reconstruct(x: Self::T) -> Self;
    }

    impl<T: ?Sized> CPointerRep for *const T
    where
        <T as std::ptr::Pointee>::Metadata: CTypeBridge,
    {
        default type T = <(*const (), <T as std::ptr::Pointee>::Metadata) as CTypeBridge>::Type;

        #[inline]
        default fn split(self) -> Self::T {
            let x: (*const (), <T as std::ptr::Pointee>::Metadata) =
                (self.cast(), std::ptr::metadata(self));
            let x = x.marshal();
            let x = std::mem::ManuallyDrop::new(x);

            // SAFETY: We know that the two types are the same.
            unsafe { std::mem::transmute_copy(&x) }
        }

        #[inline]
        default unsafe fn reconstruct(x: Self::T) -> Self {
            let x = std::mem::ManuallyDrop::new(x);

            // SAFETY: We know that the two types are the same.
            let x: <(*const (), <T as std::ptr::Pointee>::Metadata) as CTypeBridge>::Type =
                std::mem::transmute_copy(&x);
            let (ptr, metadata) =
                <(*const (), <T as std::ptr::Pointee>::Metadata) as CTypeBridge>::demarshal(x);
            std::ptr::from_raw_parts(ptr.cast(), metadata)
        }
    }

    impl<T: Sized> CPointerRep for *const T
    where
        <T as std::ptr::Pointee>::Metadata: CTypeBridge,
    {
        type T = *const ();

        fn split(self) -> Self::T {
            self.cast()
        }

        unsafe fn reconstruct(x: Self::T) -> Self {
            x.cast()
        }
    }

    impl<T: ?Sized> CPointerRep for *mut T
    where
        <T as std::ptr::Pointee>::Metadata: CTypeBridge,
    {
        default type T = <(*mut (), <T as std::ptr::Pointee>::Metadata) as CTypeBridge>::Type;

        #[inline]
        default fn split(self) -> Self::T {
            let x: (*mut (), <T as std::ptr::Pointee>::Metadata) =
                (self.cast(), std::ptr::metadata(self));
            let x = x.marshal();
            let x = std::mem::ManuallyDrop::new(x);

            // SAFETY: We know that the two types are the same.
            unsafe { std::mem::transmute_copy(&x) }
        }

        #[inline]
        default unsafe fn reconstruct(x: Self::T) -> Self {
            let x = std::mem::ManuallyDrop::new(x);

            // SAFETY: We know that the two types are the same.
            let x: <(*mut (), <T as std::ptr::Pointee>::Metadata) as CTypeBridge>::Type =
                std::mem::transmute_copy(&x);
            let (ptr, metadata) =
                <(*mut (), <T as std::ptr::Pointee>::Metadata) as CTypeBridge>::demarshal(x);
            std::ptr::from_raw_parts_mut(ptr.cast(), metadata)
        }
    }

    impl<T: Sized> CPointerRep for *mut T
    where
        <T as std::ptr::Pointee>::Metadata: CTypeBridge,
    {
        type T = *mut ();

        #[inline]
        fn split(self) -> Self::T {
            self.cast()
        }

        #[inline]
        unsafe fn reconstruct(x: Self::T) -> Self {
            x.cast()
        }
    }

    impl<'a, T: ?Sized> CPointerRep for &'a T
    where
        <T as std::ptr::Pointee>::Metadata: CTypeBridge,
    {
        type T = <*const T as CPointerRep>::T;

        #[inline]
        fn split(self) -> Self::T {
            <*const T as CPointerRep>::split(self)
        }

        #[inline]
        unsafe fn reconstruct(x: Self::T) -> Self {
            let x: *const T = <*const T as CPointerRep>::reconstruct(x);
            &*x
        }
    }

    impl<'a, T: ?Sized> CPointerRep for &'a mut T
    where
        <T as std::ptr::Pointee>::Metadata: CTypeBridge,
    {
        type T = <*mut T as CPointerRep>::T;

        #[inline]
        fn split(self) -> Self::T {
            <*mut T as CPointerRep>::split(self)
        }

        #[inline]
        unsafe fn reconstruct(x: Self::T) -> Self {
            let x: *mut T = <*mut T as CPointerRep>::reconstruct(x);
            &mut *x
        }
    }
}
