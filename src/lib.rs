// Copyright 2016 Kyle Mayes
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! This crate provides a compiler plugin, `easy_plugin!`, which makes it easier to write compiler
//! plugins.
//!
//! `easy_plugin!` generates a wrapper function around your plugin function which handles argument
//! parsing and error reporting for you, significantly reducing the time it takes to write a plugin.
//!
//! First, here is a trivial example.
//!
//! ```ignore
//! #![feature(plugin, plugin_registrar, rustc_private)]
//! #![plugin(easy_plugin)]
//!
//! #[allow(plugin_as_library)]
//! extern crate easy_plugin;
//!
//! use easy_plugin::{PluginResult};
//!
//! // rustc_plugin and syntax imports...
//!
//! easy_plugin! {
//!     struct Arguments { $a:ident }
//!
//!     /// My plugin.
//!     pub fn expand_plugin(
//!         context: &mut ExtCtxt, span: Span, arguments: Arguments
//!     ) -> PluginResult<Box<MacResult>> {
//!         println!("{:?}", arguments.a);
//!         Ok(DummyResult::any(span))
//!     }
//! }
//!
//! #[plugin_registrar]
//! pub fn plugin_registrar(registry: &mut Registry) {
//!     registry.register_macro("plugin", expand_plugin);
//! }
//! ```
//!
//! In this example, note that the arguments of the plugin function `expand_plugin` differ from a
//! typical plugin function in that the last argument is of type `Arguments` rather than
//! `&[TokenTree]`. This is because the generated wrapper function handles argument parsing for you.
//! The definition of the `Arguments` struct above `expand_plugin` provides the argument
//! specification and the generated wrapper function parses the arguments and stores them in an
//! instance of `Arguments`.
//!
//! In this example, the argument specification consists of `$a:ident`, which means that the only
//! argument this plugin will accept is a single identifier which will be stored in a field named
//! `a` in the `Arguments` struct. For more information on argument specifications, see the relevant
//! section [below](#specifications).
//!
//! If the arguments do not match the argument specification or your plugin function returns `Err`,
//! the wrapper function will report an error with `ExtCtxt::span_err` for you.
//!
//! Note that the `expand_plugin` function is public and has a documentation comment. The visibility
//! and attributes applied to your plugin function (including documentation comments) will be
//! applied to the wrapper function. In this example, the wrapper function will be public and have
//! a documentation comment.
//!
//! # Specifications
//!
//! Plugin argument specifications are very similar to the argument specifications you are used to
//! writing for macros. There are two primary differences: no restrictions on ordering and
//! additional types of named specifiers.
//!
//! | Name    | Description                            |  Storage Type         |
//! |:--------|:---------------------------------------|:----------------------|
//! | `attr`  | An attribute.                          | `Attribute`           |
//! | `binop` | A binary operator.                     | `Spanned<BinOpToken>` |
//! | `block` | A brace-delimited statement sequence.  | `P<Block>`            |
//! | `delim` | A delimited token tree sequence.       | `Spanned<Delimited>`  |
//! | `expr`  | An expression.                         | `P<Expr>`             |
//! | `ident` | An identifier.                         | `Spanned<Ident>`      |
//! | `item`  | An item.                               | `P<Item>`             |
//! | `lftm`  | A lifetime.                            | `Spanned<Name>`       |
//! | `lit`   | A literal.                             | `Lit`                 |
//! | `meta`  | A "meta" item, as found in attributes. | `P<MetaItem>`         |
//! | `pat`   | A pattern.                             | `P<Pat>`              |
//! | `path`  | A qualified name.                      | `Path`                |
//! | `stmt`  | A single statement.                    | `Stmt`                |
//! | `ty`    | A type.                                | `P<Ty>`               |
//! | `tok`   | A single token.                        | `Spanned<Token>`      |
//! | `tt`    | A single token tree.                   | `TokenTree`           |
//!
//! In addition to the specifiers above, there is also a specifier for each [`extractor`][extractor]
//! function. For example, the specifier for the
//! [`extractor::lit_to_str`](extractor/fn.lit_to_str.html) function is `lit_str`. The storage type
//! for these specifiers is the return type of the corresponding [`extractor`][extractor] function.
//! For example, the storage type of the `lit_str` specifier is `(String, StrStyle)`.
//!
//! [extractor]: extractor/index.html
//!
//! ## Sequences
//!
//! Plugin argument specifications support sequences that are very similar to the sequences in macro
//! argument specifications. For example, the following plugin argument specification matches zero
//! or more comma-separated parenthesized binary expressions.
//!
//! ```ignore
//! $(($left:ident $operator:binop $right:ident)), *
//! ```
//!
//! In addition to the `*` and `+` sequence operators, there is also a `?` operator which allows for
//! sequences with either zero or one repetitions. This operator does not support separators.  For
//! example, the following plugin argument specification can match either a binary expression or
//! nothing at all.
//!
//! ```ignore
//! $($left:ident $operator:binop $right:ident)?
//! ```
//!
//! Named specifiers that occur in sequences cannot be stored directly as their storage type because
//! there may be more than one or none at all. For this reason, named specifiers that occur in
//! sequences have the storage type of either `Vec<$type>` or `Option<$type>` where `$type` is the
//! base storage type. `Vec<$type>` is used for `*` and `+` sequences and `Option<$type>` is used
//! for `?` sequences.
//!
//! An additional level of `Vec` is added for each sequence level. For example, in the plugin
//! argument specification below, `$b:ident` occurs two sequences deep. The storage type for `b` in
//! this case would be `Vec<Vec<syntax::ast::Ident>>`.
//!
//! ```ignore
//! $($a:ident $($b:ident)*)*
//! ```
//!
//! ## Named Sequences
//!
//! There are also named sequences, which behave rather differently than regular sequences. Named
//! sequences cannot contain named specifiers and instead consist of specific token trees that you
//! wish to be counted. For example, the following plugin argument specification will match
//! either `pub struct { }` or just `struct { }`.
//!
//! ```ignore
//! $public:(pub)? struct { }
//! ```
//!
//! These named sequences allow the usage of the same suffixes as regular sequences. The `*`, `+`,
//! and `?` operators are supported and separators are supported for the `*` and `+` operators. For
//! example, the following plugin argument specification matches any number of comma-separated `A`s.
//!
//! ```ignore
//! $a:(A), *
//! ```
//!
//! Because named sequences are counted, the storage types are simply `usize` for `*` and `+` named
//! sequences and `bool` for `?`named sequences.
//!
//! ## Enums
//!
//! There are also enumerated specifiers, which allow for a choice of possible values. For example,
//! the following plugin argument specification will match either an identifier or a meta item.
//!
//! ```ignore
//! $e:{A($a:ident), B($b:meta)}
//! ```
//!
//! The storage types for enumerated specifiers are generated enums. For example, the storage type
//! for `e` above would be the following enum.
//!
//! ```ignore
//! #[derive(Debug)]
//! enum e_Enum {
//!     A { a: Spanned<Ident> },
//!     B { b: P<MetaItem> },
//! }
//! ```

#![cfg_attr(not(feature="syntex"), feature(plugin, plugin_registrar, rustc_private))]

#![cfg_attr(not(feature="syntex"), plugin(synthax))]

#![warn(missing_copy_implementations, missing_debug_implementations, missing_docs)]

#![cfg_attr(feature="clippy", plugin(clippy))]
#![cfg_attr(feature="clippy", warn(clippy))]

#[cfg(feature="syntex")]
extern crate syntex as rustc_plugin;
#[cfg(feature="syntex")]
extern crate syntex_syntax as syntax;
#[cfg(feature="syntex")]
extern crate syntex_errors as rustc_errors;
#[cfg(not(feature="syntex"))]
extern crate rustc_plugin;
#[cfg(not(feature="syntex"))]
extern crate syntax;
#[cfg(not(feature="syntex"))]
extern crate rustc_errors as rustc_errors;

extern crate easy_plugin_parsers as parsers;
extern crate synthax;

pub use parsers::extractor;
pub use parsers::{PluginResult};
pub use parsers::arguments::*;
pub use parsers::specification::*;

mod utility;
pub use utility::{PluginResultExt, ToError};

mod ast { include!(concat!(env!("OUT_DIR"), "/ast.rs")); }

include!(concat!(env!("OUT_DIR"), "/lib.rs"));
