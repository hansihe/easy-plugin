#![feature(plugin_registrar, rustc_private)]

#![cfg_attr(feature="clippy", feature(plugin))]
#![cfg_attr(feature="clippy", plugin(clippy))]
#![cfg_attr(feature="clippy", warn(clippy))]

extern crate rustc;
extern crate syntax;

use rustc::plugin::{Registry};

use syntax::ast::{TokenTree};
use syntax::codemap::{Span};
use syntax::ext::base::{ExtCtxt, DummyResult, MacResult};

mod utility;

mod arguments;
pub use self::arguments::*;

mod specification;
pub use self::specification::*;

/// A result type suitable for reporting errors in plugins.
pub type PluginResult<T> = Result<T, (Span, String)>;

#[doc(hidden)]
pub fn easy_plugin(
    context: &mut ExtCtxt, span: Span, arguments: &[TokenTree]
) -> PluginResult<Box<MacResult + 'static>> {
    Ok(DummyResult::any(span))
}

#[doc(hidden)]
pub fn expand_easy_plugin(
    context: &mut ExtCtxt, span: Span, arguments: &[TokenTree]
) -> Box<MacResult + 'static> {
    match easy_plugin(context, span, arguments) {
        Ok(result) => result,
        Err((span, message)) => {
            context.span_err(span, &message);
            DummyResult::any(span)
        },
    }
}

#[doc(hidden)]
#[plugin_registrar]
pub fn plugin_registrar(registry: &mut Registry) {
    registry.register_macro("easy_plugin", expand_easy_plugin);
}
