#ifndef FIMO_VTABLE_H
#define FIMO_VTABLE_H

#include <fimo_std/async.h>
#include <fimo_std/context.h>
#include <fimo_std/module.h>
#include <fimo_std/tracing.h>

/// VTable of a `FimoContext`.
///
/// The abi of this type is semi-stable, where given two compatible versions `v1` and `v2` with
/// `v1 <= v2`, a pointer to the vtable in `v2`, i.e., `FimoContextVTable_v2*` can be cast to a
/// pointer to the vtable in version `v1`, or `FimoContextVTable_v1*`. To that end, we are allowed
/// to add new fields to this struct and restricting the alignment. Further, to detect a version
/// mismatch, we require that `FimoContextVTableHeader` is always the first member of the VTable.
typedef struct FimoContextVTable {
    FimoContextVTableHeader header;
    FimoContextCoreVTableV0 core;
    FimoTracingVTableV0 tracing_v0;
    FimoModuleVTableV0 module_v0;
    FimoAsyncVTableV0 async_v0;
} FimoContextVTable;

#endif // FIMO_VTABLE_H
