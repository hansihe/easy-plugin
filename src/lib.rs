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
//! parsing and error reporting for you, significantly reducing the effort required to write a
//! plugin.
//!
//! A usage of `easy_plugin!` consists of one or more `enum` or `struct` argument specifications
//! followed by a plugin function. Here is a trivial example with only one argument specification
//! which accepts an identifier.
//!
//! ```ignore
//! easy_plugin! {
//!     struct Arguments { $a:ident }
//!
//!     /// My trivial plugin.
//!     pub fn expand_trivial_plugin(
//!         _: &mut ExtCtxt, span: Span, arguments: Arguments
//!     ) -> PluginResult<Box<MacResult>> {
//!         println!("{:?}", arguments.a);
//!         Ok(DummyResult::any(span))
//!     }
//! }
//! ```
//!
//! Note that the third argument of the plugin function differs from the usual signature of a plugin
//! function in that the type is `Arguments` instead of `&[TokenTree]`. This is because the
//! generated wrapper function handles argument parsing and stores the parsed arguments into a
//! generated struct named `Arguments`.
//!
//! The type you specify for the third argument of the plugin function will determine which of the
//! argument specifications will be used to parse the plugin arguments. Here is an example with an
//! `enum` argument specification that accepts either an attribute or a type.
//!
//! ```ignore
//! easy_plugin! {
//!     enum Enum {
//!         Attribute { $attr:attr },
//!         Type { $ty:ty },
//!     }
//!
//!     /// My `enum` plugin.
//!     pub fn expand_enum_plugin(
//!         _: &mut ExtCtxt, span: Span, arguments: Enum
//!     ) -> PluginResult<Box<MacResult>> {
//!         match arguments {
//!             Enum::Attribute { attr } => println!("{:?}", attr),
//!             Enum::Type { ty } => println!("{:?}", ty),
//!         }
//!         Ok(DummyResult::any(span))
//!     }
//! }
//! ```
//!
//! Every argument specification can use any previous argument specification as a part of itself.
//! Here is an example with two argument specifications that accepts two comma-separated unary or
//! binary expressions.
//!
//! ```ignore
//! easy_plugin! {
//!     enum Expr {
//!         Binary { $left:expr $op:binop $right:expr },
//!         Unary { $op:binop $expr:expr },
//!     }
//!
//!     struct Arguments { $a:$Expr, $b:$Expr }
//!
//!     /// My expression plugin.
//!     pub fn expand_expression_plugin(
//!         _: &mut ExtCtxt, span: Span, arguments: Arguments
//!     ) -> PluginResult<Box<MacResult>> {
//!         match arguments.a {
//!             Expr::Binary { left, op, right } => println!("{:?}, {:?}, {:?}", left, op, right),
//!             Expr::Unary { op, expr } => println!("{:?}, {:?}", op, expr),
//!         }
//!         Ok(DummyResult::any(span))
//!     }
//! }
//! ```
//!
//! Finally, note that the `expand_expression_plugin` function is public and has a documentation
//! comment. The visibility and attributes applied to your plugin function (including documentation
//! comments) will be removed and applied to the generated wrapper function instead. In this
//! example, the wrapper function will be public and have a documentation comment.
//!
//! # Specifications
//!
//! `easy_plugin!` argument specifications are very similar to the argument specifications you are
//! used to writing for macros. There are three primary differences: inclusion of other argument
//! specifications (as seen above), no restrictions on ordering, and additional types of named
//! specifiers.
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
//! Argument specifications support sequences that are very similar to the sequences in macro
//! argument specifications. For example, the following argument specification matches zero
//! or more comma-separated parenthesized binary expressions.
//!
//! ```ignore
//! $(($left:ident $op:binop $right:ident)), *
//! ```
//!
//! In addition to the `*` and `+` sequence operators, there is also a `?` operator which allows for
//! sequences with either zero or one repetitions. This operator does not support separators.  For
//! example, the following argument specification can match either a binary expression or
//! nothing at all.
//!
//! ```ignore
//! $($left:ident $op:binop $right:ident)?
//! ```
//!
//! Named specifiers that occur in sequences cannot be stored directly as their storage type because
//! there may be more than one or none at all. For this reason, named specifiers that occur in
//! sequences have the storage type of either `Vec<$type>` or `Option<$type>` where `$type` is the
//! base storage type. `Vec<$type>` is used for `*` and `+` sequences and `Option<$type>` is used
//! for `?` sequences.
//!
//! An additional level of `Vec` or `Option` is added for each sequence level. For example, in the
//! argument specification below, `$b:ident` occurs two sequence levels deep. The storage type for
//! `b` in this case would be `Vec<Vec<Spanned<Ident>>>`.
//!
//! ```ignore
//! $($a:ident $($b:ident)*)*
//! ```
//!
//! ## Named Sequences
//!
//! Argument specifications also support named sequences, which behave rather differently than
//! regular sequences. Named sequences cannot contain named specifiers and instead consist of
//! specific token trees that you wish to be counted. For example, the following argument
//! specification will match either `pub struct { }` or just `struct { }`.
//!
//! ```ignore
//! $public:(pub)? struct { }
//! ```
//!
//! These named sequences allow the usage of the same suffixes as regular sequences. The `*`, `+`,
//! and `?` operators are supported and separators are supported for the `*` and `+` operators. For
//! example, the following argument specification matches any number of comma-separated `A`s.
//!
//! ```ignore
//! $a:(A), *
//! ```
//!
//! Because named sequences are counted, the storage types are simply `usize` for `*` and `+` named
//! sequences and `bool` for `?`named sequences.

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

mod expr;
mod ast { include!(concat!(env!("OUT_DIR"), "/ast.rs")); }

include!(concat!(env!("OUT_DIR"), "/lib.rs"));
