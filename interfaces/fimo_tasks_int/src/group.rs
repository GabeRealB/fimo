//! Runtime group definition.

use fimo_ffi::{interface, DynObj, ObjArc, Vec};

interface! {
    #![interface_cfg(
        abi(explicit(abi = "C-unwind")),
        uuid = "111ce8ab-fc38-461f-85a5-9bb3cdd9cc91",
    )]

    /// Interface of a runtime group.
    pub interface IGroup: marker Send + marker Sync {
        /// Checks whether the current thread is owned by
        /// the group.
        fn is_owned_by(&self) -> bool;

        /// Name of the group.
        fn group_name(&self) -> &str;

        /// Fetches the number of worker threads in the group.
        fn group_size(&self) -> usize;

        /// Fetches a copy of all queues contained in the group.
        fn queues(&self) -> Vec<ObjArc<DynObj<dyn IQueue + '_>>>;
    }
}

interface! {
    #![interface_cfg(
        abi(explicit(abi = "C-unwind")),
        uuid = "9b58dde3-a2a9-4de7-aedd-67a4f013ff72",
    )]

    /// Interface of a group queue.
    pub interface IQueue: marker Send + marker Sync {
        /// Checks whether the current thread is owned by
        /// the group.
        fn is_owned_by(&self) -> bool;

        /// Fetches the number of worker threads in the group.
        fn group_size(&self) -> usize;
    }
}
