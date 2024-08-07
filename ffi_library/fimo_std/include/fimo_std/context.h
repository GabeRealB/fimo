#ifndef FIMO_CONTEXT_H
#define FIMO_CONTEXT_H

#include <fimo_std/error.h>
#include <fimo_std/utils.h>
#include <fimo_std/version.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Context of the fimo std.
 *
 * The context is an opaque object that can only be accessed through
 * the provided vtable, which is also opaque.
 */
typedef struct FimoContext {
    void *data;
    const void *vtable;
} FimoContext;

/**
 * Fimo std structure types.
 */
typedef enum FimoStructType {
    FIMO_STRUCT_TYPE_TRACING_CREATION_CONFIG,
    FIMO_STRUCT_TYPE_TRACING_METADATA,
    FIMO_STRUCT_TYPE_TRACING_SPAN_DESC,
    FIMO_STRUCT_TYPE_TRACING_SPAN,
    FIMO_STRUCT_TYPE_TRACING_EVENT,
    FIMO_STRUCT_TYPE_TRACING_SUBSCRIBER,
    FIMO_STRUCT_TYPE_MODULE_EXPORT,
    FIMO_STRUCT_TYPE_MODULE_INFO,
    FIMO_STRUCT_TYPE_FORCE32 = 0x7FFFFFFF
} FimoStructType;

/**
 * Base structure for a read-only pointer chain.
 */
typedef struct FimoBaseStructIn {
    FimoStructType type;
    const struct FimoBaseStructIn *next;
} FimoBaseStructIn;

/**
 * Base structure for a pointer chain.
 */
typedef struct FimoBaseStructOut {
    FimoStructType type;
    struct FimoBaseStructOut *next;
} FimoBaseStructOut;

/**
 * Header of all VTables of a `FimoContext`, for all future versions.
 *
 * May never be changed, since we rely on it to determine whether a
 * given `FimoContext` instance is compatible with the definitions
 * available to us.
 */
typedef struct FimoContextVTableHeader {
    FimoResult (*check_version)(void *, const FimoVersion *);
} FimoContextVTableHeader;

/**
 * Core VTable of a `FimoContext`.
 *
 * Changing the VTable is a breaking change.
 */
typedef struct FimoContextVTableV0 {
    void (*acquire)(void *);
    void (*release)(void *);
} FimoContextCoreVTableV0;

/**
 * Initializes a new context with the given options.
 *
 * If `options` is `NULL`, the context is initialized with the default options,
 * otherwise `options` must be an array terminated with a `NULL` element. The
 * initialized context is written to `context`. In case of an error, this function
 * cleans up the configuration options.
 *
 * @param options init options
 * @param context pointer to the context (not `NULL`)
 *
 * @return Status code.
 */
FIMO_EXPORT
FIMO_MUST_USE
FimoResult fimo_context_init(const FimoBaseStructIn **options, FimoContext *context);

/**
 * Checks the compatibility of the context version.
 *
 * This function must be called upon the acquisition of a context, that
 * was not created locally, e.g., when being passed a context from
 * another shared library. Failure of doing so, may cause undefined
 * behavior, if the context is later utilized.
 *
 * @param context the context
 *
 * @return Status code.
 */
FIMO_EXPORT
FIMO_MUST_USE
FimoResult fimo_context_check_version(FimoContext context);

/**
 * Acquires a reference to the context.
 *
 * Increases the reference count of the context. May abort the program,
 * if doing so is not possible. May only be called with a valid reference
 * to the context.
 *
 * @param context the context
 */
FIMO_EXPORT
void fimo_context_acquire(FimoContext context);

/**
 * Releases a reference to the context.
 *
 * Decrements the reference count of the context. When the reference count
 * reaches zero, this function also destroys the reference. May only be
 * called with a valid reference to the context.
 *
 * @param context the context
 */
FIMO_EXPORT
void fimo_context_release(FimoContext context);

#ifdef __cplusplus
}
#endif

#endif // FIMO_CONTEXT_H
