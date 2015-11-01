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

mod specification;
pub use self::specification::*;

/// A result type suitable for reporting errors in plugins.
pub type PluginResult<T> = Result<T, (Span, String)>;

/// Extends `Span` and types containing `Span` to allow conversion into a `PluginResult<T>`.
pub trait SpanAsError<T, S> where S: AsRef<str> {
    fn as_error(&self, message: S) -> PluginResult<T>;
}

impl<T, S> SpanAsError<T, S> for Span where S: AsRef<str> {
    fn as_error(&self, message: S) -> PluginResult<T> {
        Err((self.clone(), message.as_ref().into()))
    }
}

impl<T, S> SpanAsError<T, S> for TokenTree where S: AsRef<str> {
    fn as_error(&self, message: S) -> PluginResult<T> {
        Err((self.get_span().clone(), message.as_ref().into()))
    }
}

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
