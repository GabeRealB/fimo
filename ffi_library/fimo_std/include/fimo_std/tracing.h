#ifndef FIMO_TRACING_H
#define FIMO_TRACING_H

#include <stddef.h>

#include <fimo_std/context.h>
#include <fimo_std/error.h>
#include <fimo_std/time.h>
#include <fimo_std/utils.h>

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

#define FIMO_TRACING_EMIT_(_context, _name, _target, _level,     \
    _format, _metadata_var, _event_var, _error_var, ...)         \
    static const FimoTracingMetadata _metadata_var = {           \
        .type = FIMO_STRUCT_TYPE_TRACING_METADATA,               \
        .next = NULL,                                            \
        .name = (_name),                                         \
        .target = (_target),                                     \
        .level = (_level),                                       \
        .file_name = __FILE__,                                   \
        .line_number = __LINE__,                                 \
    };                                                           \
    static const FimoTracingEvent _event_var = {                 \
        .type = FIMO_STRUCT_TYPE_TRACING_EVENT,                  \
        .next = NULL,                                            \
        .metadata = &_metadata_var,                              \
    };                                                           \
    FimoError _error_var = fimo_tracing_event_emit_fmt(_context, \
        &_event_var, _format, __VA_ARGS__);                      \
    if (FIMO_IS_ERROR(_error_var)) {                             \
        return _error_var;                                       \
    }

/**
 * Emits a new event using the default formatter.
 *
 * @param _context the context
 * @param _name event name
 * @param _target event target
 * @param _level event level
 * @param _format printf format string
 * @param args printf format args
 */
#define FIMO_TRACING_EMIT(_context, _name, _target, _level, _format, ...)  \
    FIMO_TRACING_EMIT_(_context, _name, _target, _level, _format,          \
        FIMO_VAR(_fimo_private_metadata_), FIMO_VAR(_fimo_private_event_), \
        FIMO_VAR(_fimo_private_error_), __VA_ARGS__)

/**
 * Emits an error event using the default formatter.
 *
 * @param _context the context
 * @param _name event name
 * @param _target event target
 * @param _format printf format string
 * @param args printf format args
 */
#define FIMO_TRACING_EMIT_ERROR(_context, _name, _target, _format, ...)   \
    FIMO_TRACING_EMIT(_context, _name, _target, FIMO_TRACING_LEVEL_ERROR, \
        _format, __VA_ARGS__)

/**
 * Emits a warning event using the default formatter.
 *
 * @param _context the context
 * @param _name event name
 * @param _target event target
 * @param _format printf format string
 * @param args printf format args
 */
#define FIMO_TRACING_EMIT_WARN(_context, _name, _target, _format, ...)   \
    FIMO_TRACING_EMIT(_context, _name, _target, FIMO_TRACING_LEVEL_WARN, \
        _format, __VA_ARGS__)

/**
 * Emits an info event using the default formatter.
 *
 * @param _context the context
 * @param _name event name
 * @param _target event target
 * @param _format printf format string
 * @param args printf format args
 */
#define FIMO_TRACING_EMIT_INFO(_context, _name, _target, _format, ...)   \
    FIMO_TRACING_EMIT(_context, _name, _target, FIMO_TRACING_LEVEL_INFO, \
        _format, __VA_ARGS__)

/**
 * Emits a debug event using the default formatter.
 *
 * @param _context the context
 * @param _name event name
 * @param _target event target
 * @param _format printf format string
 * @param args printf format args
 */
#define FIMO_TRACING_EMIT_DEBUG(_context, _name, _target, _format, ...)   \
    FIMO_TRACING_EMIT(_context, _name, _target, FIMO_TRACING_LEVEL_DEBUG, \
        _format, __VA_ARGS__)

/**
 * Emits a trace event using the default formatter.
 *
 * @param _context the context
 * @param _name event name
 * @param _target event target
 * @param _format printf format string
 * @param args printf format args
 */
#define FIMO_TRACING_EMIT_TRACE(_context, _name, _target, _format, ...)   \
    FIMO_TRACING_EMIT(_context, _name, _target, FIMO_TRACING_LEVEL_TRACE, \
        _format, __VA_ARGS__)

/**
 * A call stack.
 *
 * Each call stack represents a unit of computation, like a thread.
 * A call stack is active on only one thread at any given time. The
 * active call stack of a thread can be swapped, which is useful
 * for tracing where a `M:N` threading model is used. In that case,
 * one would create one stack for each task, and activate it when
 * the task is resumed.
 */
typedef void* FimoTracingCallStack;

/**
 * Possible tracing levels.
 *
 * The levels are ordered such that given two levels
 * `lvl1` and `lvl2`, where `lvl1 >= lvl2`, then an event
 * with level `lvl2` will be traced in a context where the
 * maximum tracing level is `lvl1`.
 */
typedef enum FimoTracingLevel {
    FIMO_TRACING_LEVEL_OFF = 0,
    FIMO_TRACING_LEVEL_ERROR = 1,
    FIMO_TRACING_LEVEL_WARN = 2,
    FIMO_TRACING_LEVEL_INFO = 3,
    FIMO_TRACING_LEVEL_DEBUG = 4,
    FIMO_TRACING_LEVEL_TRACE = 5,
} FimoTracingLevel;

/**
 * Metadata for a span/event.
 */
typedef struct FimoTracingMetadata {
    /**
     * Type of the struct.
     *
     * Must be `FIMO_STRUCT_TYPE_TRACING_METADATA`.
     */
    FimoStructType type;
    /**
     * Pointer to a possible extension.
     *
     * Reserved for future use. Must be `NULL`.
     */
    const FimoBaseStructIn* next;
    /**
     * Name of the event.
     *
     * Must not be `NULL`.
     */
    const char* name;
    /**
     * Target of the event.
     *
     * Must not be `NULL`.
     */
    const char* target;
    /**
     * Level at which to trace the event.
     */
    FimoTracingLevel level;
    /**
     * Optional file name where the event took place.
     */
    const char* file_name;
    /**
     * Optional line number where the event took place.
     *
     * Use a negative number to indicate no line number.
     */
    FimoI32 line_number;
} FimoTracingMetadata;

/**
 * Descriptor of a new span.
 */
typedef struct FimoTracingSpanDesc {
    /**
     * Type of the struct.
     *
     * Must be `FIMO_STRUCT_TYPE_TRACING_SPAN_DESC`.
     */
    FimoStructType type;
    /**
     * Pointer to a possible extension.
     *
     * Reserved for future use. Must be `NULL`.
     */
    const FimoBaseStructIn* next;
    /**
     * Metadata of the span.
     *
     * Must not be `NULL`.
     */
    const FimoTracingMetadata* metadata;
} FimoTracingSpanDesc;

/**
 * A period of time, during which events can occur.
 */
typedef struct FimoTracingSpan {
    /**
     * Type of the struct.
     *
     * Must be `FIMO_STRUCT_TYPE_TRACING_SPAN`.
     */
    FimoStructType type;
    /**
     * Pointer to a possible extension.
     *
     * Reserved for future use.
     */
    FimoBaseStructOut* next;
    /**
     * Id assigned to the span.
     */
    void* span_id;
} FimoTracingSpan;

/**
 * An event to be traced.
 */
typedef struct FimoTracingEvent {
    /**
     * Type of the struct.
     *
     * Must be `FIMO_STRUCT_TYPE_TRACING_EVENT`.
     */
    FimoStructType type;
    /**
     * Pointer to a possible extension.
     *
     * Reserved for future use. Must be `NULL`.
     */
    const FimoBaseStructIn* next;
    /**
     * Metadata of the event.
     *
     * Must not be `NULL`.
     */
    const FimoTracingMetadata* metadata;
} FimoTracingEvent;

/**
 * Signature of a message formatter.
 *
 * It is not an error to format only a part of the message.
 *
 * @param arg0 destination buffer
 * @param arg1 destination buffer size
 * @param arg2 data to format
 * @param arg3 number of written bytes of the formatter
 * @return Status code.
 */
typedef FimoError (*FimoTracingFormat)(char*, size_t, const void*, size_t*);

/**
 * VTable of a tracing subscriber.
 *
 * Adding/removing functionality to a subscriber through this table
 * is a breaking change, as a subscriber may be implemented from
 * outside the library.
 */
typedef struct FimoTracingSubscriberVTable {
    /**
     * Destroys the subscriber.
     *
     * @param arg0 pointer to the subscriber
     */
    void (*destroy)(void*);
    /**
     * Creates a new stack.
     *
     * @param arg0 pointer to the subscriber
     * @param arg1 time of the event
     * @param arg2 pointer to the new stack
     * @return Status code.
     */
    FimoError (*call_stack_create)(void*, const FimoTime*, void**);
    /**
     * Destroys a stack.
     *
     * @param arg0 pointer to the subscriber
     * @param arg1 time of the event
     * @param arg2 the stack
     */
    void (*call_stack_destroy)(void*, const FimoTime*, void*);
    /**
     * Marks the stack as unblocked.
     *
     * @param arg0 pointer to the subscriber
     * @param arg1 time of the event
     * @param arg2 the stack
     */
    void (*call_stack_unblock)(void*, const FimoTime*, void*);
    /**
     * Marks the stack as suspended/blocked.
     *
     * @param arg0 pointer to the subscriber
     * @param arg1 time of the event
     * @param arg2 the stack
     * @param arg3 whether to block the stack
     */
    void (*call_stack_suspend)(void*, const FimoTime*, void*, bool);
    /**
     * Marks the stack as resumed.
     *
     * @param arg0 pointer to the subscriber
     * @param arg1 time of the event
     * @param arg2 the stack
     */
    void (*call_stack_resume)(void*, const FimoTime*, void*);
    /**
     * Creates a new span.
     *
     * @param arg0 pointer to the subscriber
     * @param arg2 descriptor of the span
     * @param arg3 formatted span message
     * @param arg4 length of the span message
     * @param arg5 the call stack
     * @param arg6 pointer to the new span
     * @return Status code.
     */
    FimoError (*span_create)(void*, const FimoTime*,
        const FimoTracingSpanDesc*, const char*, size_t, void*,
        void**);
    /**
     * Exits and destroys a span.
     *
     * @param arg0 pointer to the subscriber
     * @param arg1 time of the event
     * @param arg2 the call stack
     * @param arg3 the span
     */
    void (*span_destroy)(void*, const FimoTime*, void*, void*);
    /**
     * Emits an event.
     *
     * @param arg0 pointer to the subscriber
     * @param arg1 time of the event
     * @param arg2 the call stack
     * @param arg3 the event to emit
     * @param arg4 formatted message of the event
     * @param arg5 length of the event message
     */
    void (*event_emit)(void*, const FimoTime*, void*,
        const FimoTracingEvent*, const char*, size_t);
    /**
     * Flushes the messages of the subscriber.
     *
     * @param arg0 pointer to the subscriber
     */
    void (*flush)(void*);
} FimoTracingSubscriberVTable;

/**
 * A subscriber for tracing events.
 *
 * The main function of the tracing backend is managing and routing
 * tracing events to subscribers. Therefore it does not consume any
 * events on its own, which is the task of the subscribers. Subscribers
 * may utilize the events in any way they deem fit.
 */
typedef struct FimoTracingSubscriber {
    /**
     * Type of the struct.
     *
     * Must be `FIMO_STRUCT_TYPE_TRACING_SUBSCRIBER`.
     */
    FimoStructType type;
    /**
     * Pointer to a possible extension.
     *
     * Reserved for future use. Must be `NULL`.
     */
    const struct FimoBaseStructIn* next;
    /**
     * Pointer to the subscriber.
     */
    void* ptr;
    /**
     * Pointer to the vtable of the subscriber (not `Null`).
     */
    const FimoTracingSubscriberVTable* vtable;
} FimoTracingSubscriber;

/**
 * Configuration for the tracing backend.
 *
 * Can be passed when creating the context.
 */
typedef struct FimoTracingCreationConfig {
    /**
     * Type of the struct.
     *
     * Must be `FIMO_STRUCT_TYPE_TRACING_CREATION_CONFIG`.
     */
    FimoStructType type;
    /**
     * Pointer to a possible extension.
     *
     * Reserved for future use. Must be `NULL`.
     */
    const struct FimoBaseStructIn* next;
    /**
     * Size of the per-thread buffer used for formatting messages.
     */
    size_t format_buffer_size;
    /**
     * Maximum level for which to consume tracing events.
     */
    FimoTracingLevel maximum_level;
    /**
     * Array of subscribers to register with the tracing backend.
     *
     * Must be `NULL` when there are no subscribers. The ownership
     * of the subscribers is transferred to the context.
     */
    FimoTracingSubscriber* subscribers;
    /**
     * Number of subscribers to register with the tracing backend.
     *
     * Must match the number of subscribers present in `subscribers`.
     */
    size_t subscriber_count;
} FimoTracingCreationConfig;

/**
 * Creates a new empty call stack.
 *
 * If successful, the new call stack is marked as suspended, and written
 * into `call_stack`. The new call stack is not set to be the active call
 * stack.
 *
 * @param context the context
 * @param call_stack pointer to the resulting call stack
 *
 * @return Status code.
 */
FIMO_MUST_USE
FimoError fimo_tracing_call_stack_create(FimoContext context,
    FimoTracingCallStack* call_stack);

/**
 * Destroys an empty call stack.
 *
 * Marks the completion of a task. Before calling this function, the
 * call stack must be empty, i.e., there must be no active spans on
 * the stack, and must not be active. If successful, the call stack
 * may not be used afterwards. The active call stack of the thread
 * is destroyed automatically, on thread exit or during destruction
 * of `context`. The caller must own the call stack uniquely.
 *
 * @param context the context
 * @param call_stack the call stack to destroy
 *
 * @return Status code.
 */
FIMO_MUST_USE
FimoError fimo_tracing_call_stack_destroy(FimoContext context,
    FimoTracingCallStack call_stack);

/**
 * Switches the call stack of the current thread.
 *
 * If successful, `new_call_stack` will be used as the active call
 * stack of the calling thread. The old call stack is written into
 * `old_call_stack`, enabling the caller to switch back to it afterwards.
 * `new_call_stack` must be in a suspended, but unblocked, state and not be
 * active. The active call stack must also be in a suspended state, but may
 * also be blocked.
 *
 * @param context the context
 * @param new_call_stack new call stack
 * @param old_call_stack location to store the old call stack into
 *
 * @return Status code.
 */
FIMO_MUST_USE
FimoError fimo_tracing_call_stack_switch(FimoContext context,
    FimoTracingCallStack new_call_stack, FimoTracingCallStack* old_call_stack);

/**
 * Unblocks a blocked call stack.
 *
 * Once unblocked, the call stack may be resumed. The call stack
 * may not be active and must be marked as blocked.
 *
 * @param context the context
 * @param call_stack the call stack to unblock
 *
 * @return Status code.
 */
FIMO_MUST_USE
FimoError fimo_tracing_call_stack_unblock(FimoContext context,
    FimoTracingCallStack call_stack);

/**
 * Marks the current call stack as being suspended.
 *
 * While suspended, the call stack can not be utilized for tracing
 * messages. The call stack optionally also be marked as being
 * blocked. In that case, the call stack must be unblocked prior
 * to resumption.
 *
 * @param context the context
 * @param block whether to mark the call stack as blocked
 *
 * @return Status code.
 */
FIMO_MUST_USE
FimoError fimo_tracing_call_stack_suspend_current(FimoContext context,
    bool block);

/**
 * Marks the current call stack as being resumed.
 *
 * Once resumed, the context can be used to trace messages. To be
 * successful, the current call stack must be suspended and unblocked.
 *
 * @param context the context.
 *
 * @return Status code.
 */
FIMO_MUST_USE
FimoError fimo_tracing_call_stack_resume_current(FimoContext context);

/**
 * Creates a new span with the standard formatter and enters it.
 *
 * If successful, the newly created span is used as the context for
 * succeeding events. The message is formatted as if it were
 * formatted by a call to `snprintf`. The message may be cut of,
 * if the length exceeds the internal formatting buffer size.  The
 * contents of `span_desc` must remain valid until the span is destroyed.
 *
 * @param context the context
 * @param span_desc descriptor of the new span
 * @param span pointer to the resulting span
 * @param format formatting string
 *
 * @return Status code.
 */
FIMO_MUST_USE
FimoError fimo_tracing_span_create_fmt(FimoContext context,
    const FimoTracingSpanDesc* span_desc, FimoTracingSpan* span,
    FIMO_PRINT_F_FORMAT const char* format, ...) FIMO_PRINT_F_FORMAT_ATTR(4, 5);

/**
 * Creates a new span with a custom formatter and enters it.
 *
 * If successful, the newly created span is used as the context for
 * succeeding events. The backend may use a formatting buffer of a
 * fixed size. The formatter is expected to cut-of the message after
 * reaching that specified size. The contents of `span_desc` must
 * remain valid until the span is destroyed.
 *
 * @param context the context
 * @param span_desc descriptor of the new span
 * @param span pointer to the resulting span
 * @param format custom formatting function
 * @param data custom formatting data
 *
 * @return Status code.
 */
FIMO_MUST_USE
FimoError fimo_tracing_span_create_custom(FimoContext context,
    const FimoTracingSpanDesc* span_desc, FimoTracingSpan* span,
    FimoTracingFormat format, const void* data);

/**
 * Exits and destroys a span.
 *
 * If successful, succeeding events won't occur inside the context of the
 * exited span anymore. `span` must be the span at the top of the current
 * call stack. The span may not be in use prior to a call to this function,
 * and may not be used afterwards.
 *
 * @param context the context
 * @param span the span to destroy
 *
 * @return Status code.
 */
FIMO_MUST_USE
FimoError fimo_tracing_span_destroy(FimoContext context,
    FimoTracingSpan* span);

/**
 * Emits a new event with the standard formatter.
 *
 * The message is formatted as if it were formatted by a call to `snprintf`.
 * The message may be cut of, if the length exceeds the internal formatting
 * buffer size.
 *
 * @param context the context
 * @param event the event to emit
 * @param format formatting string
 *
 * @return Status code.
 */
FIMO_MUST_USE
FimoError fimo_tracing_event_emit_fmt(FimoContext context,
    const FimoTracingEvent* event, FIMO_PRINT_F_FORMAT const char* format,
    ...) FIMO_PRINT_F_FORMAT_ATTR(3, 4);

/**
 * Emits a new event with a custom formatter.
 *
 * The backend may use a formatting buffer of a fixed size. The formatter is
 * expected to cut-of the message after reaching that specified size.
 *
 * @param context the context
 * @param event the event to emit
 * @param format custom formatting function
 * @param data custom data to format
 *
 * @return Status code.
 */
FIMO_MUST_USE
FimoError fimo_tracing_event_emit_custom(FimoContext context,
    const FimoTracingEvent* event, FimoTracingFormat format, const void* data);

/**
 * Checks whether the tracing backend is enabled.
 *
 * This function can be used to check whether to call into the backend at all.
 * Calling this function is not necessary, as the remaining functions of the
 * backend are guaranteed to return default values, in case the backend is
 * disabled.
 *
 * @param context the context.
 *
 * @return `true` if the backend is enabled.
 */
FIMO_MUST_USE
bool fimo_tracing_is_enabled(FimoContext context);

/**
 * Registers the calling thread with the tracing backend.
 *
 * The tracing of the backend is opt-in on a per thread basis, where
 * unregistered threads will behave as if the backend was disabled.
 * Once registered, the calling thread gains access to the tracing
 * backend and is assigned a new empty call stack. A registered
 * thread must be unregistered from the tracing backend before the
 * context is destroyed, by terminating the tread, or by manually
 * calling `fimo_tracing_unregister_thread()`.
 *
 * @param context the context
 *
 * @return Status code.
 */
FIMO_MUST_USE
FimoError fimo_tracing_register_thread(FimoContext context);

/**
 * Unregisters the calling thread from the tracing backend.
 *
 * Once unregistered, the calling thread looses access to the tracing
 * backend until it is registered again. The thread can not be unregistered
 * until the call stack is empty.
 *
 * @param context the context.
 *
 * @return Status code.
 */
FIMO_MUST_USE
FimoError fimo_tracing_unregister_thread(FimoContext context);

/**
 * Flushes the streams used for tracing.
 *
 * If successful, any unwritten data is written out by the individual subscribers.
 *
 * @param context the context
 *
 * @return Status code.
 */
FIMO_MUST_USE
FimoError fimo_tracing_flush(FimoContext context);

#ifdef __cplusplus
}
#endif // __cplusplus

#endif // FIMO_TRACING_H