#![cfg_attr(not(feature="syntex"), feature(plugin))]
#![cfg_attr(not(feature="syntex"), feature(plugin_registrar))]
#![cfg_attr(not(feature="syntex"), feature(rustc_private))]

#![cfg_attr(not(feature="syntex"), plugin(easy_plugin))]

#[cfg(feature="syntex")]
extern crate syntex as rustc_plugin;
#[cfg(feature="syntex")]
extern crate syntex_syntax as syntax;
#[cfg(not(feature="syntex"))]
extern crate rustc_plugin;
#[cfg(not(feature="syntex"))]
extern crate syntax;

#[cfg_attr(not(feature="syntex"), allow(plugin_as_library))]
#[macro_use]
extern crate easy_plugin;

include!(concat!(env!("OUT_DIR"), "/tests.rs"));
