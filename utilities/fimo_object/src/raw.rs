//! Definition of raw objects.
use crate::vtable::{BaseInterface, ObjectID, VTable};
use std::fmt::{Debug, Formatter, Pointer};

/// Raw representation of an immutable object.
#[repr(C)]
pub struct RawObject<T: VTable> {
    object: *const (),
    vtable: &'static T,
}

unsafe impl<T: VTable> Send for RawObject<T> where <T as VTable>::Markers: Send {}
unsafe impl<T: VTable> Sync for RawObject<T> where <T as VTable>::Markers: Sync {}

impl<T: VTable> Copy for RawObject<T> {}

impl<T: VTable> Clone for RawObject<T> {
    fn clone(&self) -> Self {
        Self {
            object: self.object,
            vtable: self.vtable,
        }
    }
}

impl<T: VTable> Debug for RawObject<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RawObject")
            .field("object", &self.object)
            .field("vtable", &format!("{:p}", self.vtable))
            .field("object_id", &self.vtable.object_id())
            .field("interface_id", &self.vtable.interface_id())
            .finish()
    }
}

impl<T: VTable> Pointer for RawObject<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Pointer::fmt(&self.object, f)
    }
}

/// Raw representation of a mutable object.
#[repr(C)]
pub struct RawObjectMut<T: VTable> {
    object: *mut (),
    vtable: &'static T,
}

unsafe impl<T: VTable> Send for RawObjectMut<T> where <T as VTable>::Markers: Send {}
unsafe impl<T: VTable> Sync for RawObjectMut<T> where <T as VTable>::Markers: Sync {}

impl<T: VTable> Copy for RawObjectMut<T> {}

impl<T: VTable> Clone for RawObjectMut<T> {
    fn clone(&self) -> Self {
        Self {
            object: self.object,
            vtable: self.vtable,
        }
    }
}

impl<T: VTable> Debug for RawObjectMut<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RawObjectMut")
            .field("object", &self.object)
            .field("vtable", &format!("{:p}", self.vtable))
            .field("object_id", &self.vtable.object_id())
            .field("interface_id", &self.vtable.interface_id())
            .finish()
    }
}

impl<T: VTable> Pointer for RawObjectMut<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Pointer::fmt(&self.object, f)
    }
}

impl<T: VTable> From<RawObjectMut<T>> for RawObject<T> {
    fn from(obj: RawObjectMut<T>) -> Self {
        Self {
            object: obj.object,
            vtable: obj.vtable,
        }
    }
}

/// Casting error.
#[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct CastError<T> {
    /// Object.
    pub obj: T,
    /// Required id.
    pub required: &'static str,
    /// Available id.
    pub available: &'static str,
}

/// Casts an object to the base object.
pub fn cast_base<T: VTable>(obj: RawObject<T>) -> RawObject<BaseInterface> {
    // safety: we assume that the start of `T` matches with `BaseInterface`.
    unsafe { std::mem::transmute(obj) }
}

/// Casts an object to the base object.
pub fn cast_base_mut<T: VTable>(obj: RawObjectMut<T>) -> RawObjectMut<BaseInterface> {
    // safety: we assume that the start of `T` matches with `BaseInterface`.
    unsafe { std::mem::transmute(obj) }
}

/// Casts the interface of the object.
pub fn try_cast<T: VTable>(
    obj: RawObject<BaseInterface>,
) -> Result<RawObject<T>, CastError<RawObject<BaseInterface>>> {
    if obj.vtable.interface_id() == T::INTERFACE_ID {
        // safety: the interface id's are unique, so we can ensure that the object
        // contains a reference to a `T`.
        let obj = unsafe { std::mem::transmute(obj) };
        Ok(obj)
    } else {
        Err(CastError {
            obj,
            required: T::INTERFACE_ID,
            available: obj.vtable.interface_id().into(),
        })
    }
}

/// Casts the interface of the object.
pub fn try_cast_mut<T: VTable>(
    obj: RawObjectMut<BaseInterface>,
) -> Result<RawObjectMut<T>, CastError<RawObjectMut<BaseInterface>>> {
    if obj.vtable.interface_id() == T::INTERFACE_ID {
        // safety: the interface id's are unique, so we can ensure that the object
        // contains a reference to a `T`.
        let obj = unsafe { std::mem::transmute(obj) };
        Ok(obj)
    } else {
        let id: &'static str = obj.vtable.interface_id().into();

        Err(CastError {
            obj,
            required: T::INTERFACE_ID,
            available: id,
        })
    }
}

/// Casts the object to a pointer to a proper type.
pub fn try_cast_obj<T: VTable, O: ObjectID>(
    obj: RawObject<T>,
) -> Result<*const O, CastError<RawObject<T>>> {
    if obj.vtable.object_id() == O::OBJECT_ID {
        let obj = obj.object as *const O;
        Ok(obj)
    } else {
        Err(CastError {
            obj,
            required: O::OBJECT_ID,
            available: obj.vtable.object_id().into(),
        })
    }
}

/// Casts the object to a pointer to a proper type.
pub fn try_cast_obj_mut<T: VTable, O: ObjectID>(
    obj: RawObjectMut<T>,
) -> Result<*mut O, CastError<RawObjectMut<T>>> {
    if obj.vtable.object_id() == O::OBJECT_ID {
        let obj = obj.object as *mut O;
        Ok(obj)
    } else {
        let id: &'static str = obj.vtable.object_id().into();

        Err(CastError {
            obj,
            required: O::OBJECT_ID,
            available: id,
        })
    }
}

/// Constructs an object from it's raw parts.
///
/// # Safety
///
/// - The vtable must have a compatible layout.
/// - The object pointer must be compatible with the vtable.
pub unsafe fn from_raw_parts<T: VTable>(obj: *const (), vtable: &'static T) -> RawObject<T> {
    RawObject {
        object: obj,
        vtable,
    }
}

/// Constructs an object from it's raw parts.
///
/// # Safety
///
/// - The vtable must have a compatible layout.
/// - The object pointer must be compatible with the vtable.
pub unsafe fn from_raw_parts_mut<T: VTable>(obj: *mut (), vtable: &'static T) -> RawObjectMut<T> {
    RawObjectMut {
        object: obj,
        vtable,
    }
}

/// Splits an object into it's raw parts.
pub fn into_raw_parts<T: VTable>(obj: RawObject<T>) -> (*const (), &'static T) {
    (obj.object, obj.vtable)
}

/// Splits an object into it's raw parts.
pub fn into_raw_parts_mut<T: VTable>(obj: RawObjectMut<T>) -> (*mut (), &'static T) {
    (obj.object, obj.vtable)
}