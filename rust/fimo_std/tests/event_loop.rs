use fimo_std::{
    r#async::{BlockingContext, EventLoop},
    context::{Context, ContextBuilder, ContextView},
    emit_trace,
    error::AnyError,
    tracing::{Config, Level, ThreadAccess, default_subscriber},
    utils::Viewable,
};
use std::{future::Future, pin::Pin, task::Poll};

#[test]
fn block_on_futures() -> Result<(), AnyError> {
    let context = ContextBuilder::new()
        .with_tracing_config(
            Config::default()
                .with_max_level(Level::Trace)
                .with_subscribers(&[default_subscriber()]),
        )
        .build()?;

    let _access = ThreadAccess::new(&context);
    let _event_loop = EventLoop::new(&context)?;

    let fut = new_nested(context.view())?;

    let blocking = BlockingContext::new(&context)?;
    let (a, b) = blocking.block_on(fut);

    assert_eq!(a, LOOP_1);
    assert_eq!(b, LOOP_2);

    Ok(())
}

const LOOP_1: usize = 5;
const LOOP_2: usize = 10;

fn new_nested(ctx: ContextView<'_>) -> Result<impl Future<Output = (usize, usize)>, AnyError> {
    let a = fimo_std::r#async::Future::new(LoopFuture::<LOOP_1>::new(ctx)).enqueue(ctx)?;
    let b = fimo_std::r#async::Future::new(LoopFuture::<LOOP_2>::new(ctx)).enqueue(ctx)?;

    let ctx = ctx.to_context();
    Ok(async move {
        emit_trace!(ctx, "Poll start");
        let a = a.await;
        emit_trace!(ctx, "A finished");
        let b = b.await;
        emit_trace!(ctx, "B finished");
        (a, b)
    })
}

struct LoopFuture<const N: usize> {
    i: usize,
    ctx: Context,
}

impl<const N: usize> LoopFuture<N> {
    fn new(ctx: ContextView<'_>) -> Self {
        Self {
            i: 0,
            ctx: ctx.to_context(),
        }
    }
}

impl<const N: usize> Future for LoopFuture<N> {
    type Output = usize;

    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        let inner = unsafe { Pin::into_inner_unchecked(self) };
        emit_trace!(&inner.ctx, "Iteration i='{}', data=`{:p}`", inner.i, inner);

        inner.i += 1;
        if inner.i < N {
            cx.waker().wake_by_ref();
            Poll::Pending
        } else {
            Poll::Ready(inner.i)
        }
    }
}
