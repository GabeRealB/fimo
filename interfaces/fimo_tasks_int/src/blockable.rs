//! Block list definition.
use std::collections::HashSet;

use fimo_ffi::ptr::IBase;
use fimo_ffi::{interface, DynObj, Object};

interface! {
    #![interface_cfg(
        abi(explicit(abi = "C-unwind")),
        uuid = "c06ff535-2944-4267-9691-8b33d979a947",
    )]

    /// Interface of a block list.
    pub interface IBlockable : marker IBase + marker Sync {
        /// Fetches the list of [`IBlockable`]'s that depend on the resource.
        fn waiter_list(&self) -> &DynObj<dyn IWaitList>;

        /// Fetches the list of [`IBlockable`]'s that depend on the resource.
        fn waiter_list_mut(&mut self) -> &mut DynObj<dyn IWaitList>;

        /// Fetches the list of [`IBlockable`]'s that the resource depends on.
        fn dependency_list(&self) -> Option<&DynObj<dyn IWaitList>>;

        /// Fetches the list of [`IBlockable`]'s that the resource depends on.
        fn dependecy_list_mut(&mut self) -> Option<&mut DynObj<dyn IWaitList>>;
    }
}

interface! {
    #![interface_cfg(
        abi(explicit(abi = "C-unwind")),
        uuid = "64d5fbd8-c560-4792-a15b-7cfc0aa1ac44",
    )]

    /// A list of [`IBlockable`].
    pub interface IWaitList : marker IBase + marker Sync {
        /// Number of elements.
        fn len(&self) -> usize;

        /// Checks whether the list is empty.
        fn is_empty(&self) -> bool;

        /// Checks whether a blockable is contained.
        fn contains(&self, blockable: *const DynObj<dyn IBlockable>) -> bool;

        /// Removes a blockable from the list.
        ///
        /// Returns `true`, if the element is contained in the list.
        fn remove(
            &mut self,
            blockable: *const DynObj<dyn IBlockable>
        ) -> bool;

        /// Pushes a new blockable to the list.
        ///
        /// Returns `true`, if the list does not contain the element.
        fn push(&mut self, blockable: *const DynObj<dyn IBlockable>) -> bool;

        /// Pops an entry from the list.
        ///
        /// Returns `None`, if the list is empty.
        fn pop(&mut self) -> Option<*const DynObj<dyn IBlockable>>;
    }
}

#[derive(Debug, Object, Default)]
#[interfaces(IBlockable)]
pub(crate) struct BlockList {
    waiter_list: WaitList,
    dependency_list: WaitList,
}

impl IBlockable for BlockList {
    fn waiter_list(&self) -> &DynObj<dyn IWaitList> {
        fimo_ffi::ptr::coerce_obj(&self.waiter_list)
    }

    fn waiter_list_mut(&mut self) -> &mut DynObj<dyn IWaitList> {
        fimo_ffi::ptr::coerce_obj_mut(&mut self.waiter_list)
    }

    fn dependency_list(&self) -> Option<&DynObj<dyn IWaitList>> {
        Some(fimo_ffi::ptr::coerce_obj(&self.dependency_list))
    }

    fn dependecy_list_mut(&mut self) -> Option<&mut DynObj<dyn IWaitList>> {
        Some(fimo_ffi::ptr::coerce_obj_mut(&mut self.dependency_list))
    }
}

#[derive(Debug, Object, Default)]
#[interfaces(IWaitList)]
pub(crate) struct WaitList {
    list: HashSet<*const DynObj<dyn IBlockable>>,
}

unsafe impl Send for WaitList where &'static DynObj<dyn IBlockable>: Send {}
unsafe impl Sync for WaitList where &'static DynObj<dyn IBlockable>: Sync {}

impl IWaitList for WaitList {
    fn len(&self) -> usize {
        self.list.len()
    }

    fn is_empty(&self) -> bool {
        self.list.is_empty()
    }

    fn contains(&self, blockable: *const DynObj<dyn IBlockable>) -> bool {
        self.list.contains(&blockable)
    }

    fn remove(&mut self, blockable: *const DynObj<dyn IBlockable>) -> bool {
        self.list.remove(&blockable)
    }

    fn push(&mut self, blockable: *const DynObj<dyn IBlockable>) -> bool {
        self.list.insert(blockable)
    }

    fn pop(&mut self) -> Option<*const DynObj<dyn IBlockable>> {
        let element = self.list.iter().copied().next();
        if let Some(element) = element {
            self.list.remove(&element);
            Some(element)
        } else {
            None
        }
    }
}
