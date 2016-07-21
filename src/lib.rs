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
//! It can be used one of two ways, one which allows for only one argument specification and another
//! that allows for multiple argument specifications.
//!
//! First, here is a trivial
//! [example](https://github.com/KyleMayes/easy-plugin/blob/master/examples/struct.rs) of the first
//! form that only allows for one argument specification.
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
//! The faux-definition of `Arguments` above `expand_plugin` provides the argument specification and
//! the generated wrapper function parses the arguments and stores them in an instance of
//! `Arguments`.
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
//! Next, here is a trivial
//! [example](https://github.com/KyleMayes/easy-plugin/blob/master/examples/enum.rs) of the second
//! form that allows for multiple argument specifications.
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
//!     enum Arguments {
//!         A { },
//!         B { $a:ident }, // <- this trailing comma is required!
//!     }
//!
//!     /// My plugin.
//!     pub fn expand_plugin(
//!         context: &mut ExtCtxt, span: Span, arguments: Arguments
//!     ) -> PluginResult<Box<MacResult>> {
//!         match arguments {
//!             Arguments::A(a) => { },
//!             Arguments::B(b) => println!("{:?}", b.a),
//!         }
//!
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
//! This form behaves much like the first, except that a parse of the arguments will be attempted
//! with each specification in the provided order until one succeeds. If every attempt fails, the
//! resulting error message will be from the final parse attempt. The results of a successful parse
//! will be stored in a struct which will then be stored in an enum variant of the same name.
//!
//! In this example, if the arguments consist of a single identifier, the first parse attempt will
//! fail but the second will succeed. The identifier will be stored in a field named `a` in a struct
//! named `B`. This struct will then be stored in the enum variant `Arguments::B`.
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
//! | `stmt`  | A single statement.                    | `P<Stmt>`             |
//! | `ty`    | A type.                                | `P<Ty>`               |
//! | `tok`   | A single token.                        | `Spanned<Token>`      |
//! | `tt`    | A single token tree.                   | `TokenTree`           |
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

#![feature(plugin, plugin_registrar, quote, rustc_private)]

#![plugin(easy_plugin_plugins)]

#![warn(missing_copy_implementations, missing_debug_implementations, missing_docs)]

#![cfg_attr(feature="clippy", plugin(clippy))]
#![cfg_attr(feature="clippy", warn(clippy))]
#![cfg_attr(feature="clippy", allow(similar_names, used_underscore_binding))]

extern crate rustc_plugin;
extern crate syntax;

use rustc_plugin::{Registry};

use syntax::ast::*;
use syntax::codemap::{Span};
use syntax::ext::base::{ExtCtxt, DummyResult, MacResult};
use syntax::ext::build::{AstBuilder};
use syntax::parse::token::{Token};
use syntax::ptr::{P};
use syntax::tokenstream::{TokenTree};

pub mod convert;

mod utility;
use utility::{ToExpr};
pub use utility::{PluginResultExt, ToError};

mod arguments;
pub use self::arguments::*;

#[macro_use]
mod specification;
pub use self::specification::*;

mod enums;
mod structs;

/// A result type suitable for reporting errors in plugins.
pub type PluginResult<T> = Result<T, (Span, String)>;

//================================================
// Functions
//================================================

/// Strips the visibility and attributes from a function and appends `_` to the name.
#[doc(hidden)]
pub fn strip_function(
    context: &mut ExtCtxt, function: P<Item>
) -> (P<Item>, Ident, Visibility, Vec<Attribute>) {
    let ident = function.ident;
    let visibility = function.vis.clone();
    let attributes = function.attrs.clone();
    let function = function.map(|mut f| {
        f.ident = context.ident_of(&format!("{}_", ident.name));
        f.vis = Visibility::Inherited;
        f.attrs = vec![];
        f
    });
    (function, ident, visibility, attributes)
}

/// Returns a function that parse arguments according the supplied specification.
#[doc(hidden)]
pub fn expand_parse(
    context: &mut ExtCtxt, span: Span, name: Ident, specification: &Specification, multiple: bool
) -> P<Item> {
    let function = if multiple {
        context.ident_of(&format!("parse{}", name.name))
    } else {
        context.ident_of("parse")
    };

    let fields = specification.iter().flat_map(|s| {
        s.to_fields(context, span, &[]).into_iter()
    }).collect::<Vec<_>>();
    let result = if fields.is_empty() {
        quote_expr!(context, $name)
    } else {
        let path = context.path(span, vec![name]);
        context.expr_struct(span, path, fields)
    };

    let specification = specification.to_expr(context, span);

    // Build the function.
    quote_item!(context,
        #[allow(non_snake_case)]
        fn $function(
            session: &::syntax::parse::ParseSess, arguments: &[::syntax::tokenstream::TokenTree]
        ) -> ::easy_plugin::PluginResult<$name> {
            ::easy_plugin::parse_args(session, arguments, &$specification.0).map(|_m| $result)
        }
    ).unwrap()
}

/// Returns an easy-plugin wrapper function.
fn expand_easy_plugin_(
    context: &mut ExtCtxt, span: Span, arguments: &[TokenTree]
) -> PluginResult<Box<MacResult + 'static>> {
    if arguments.is_empty() {
        return span.to_error("unexpected end of arguments");
    }

    match arguments[0] {
        TokenTree::Token(_, Token::Ident(ref ident)) => match &*ident.name.as_str() {
            "enum" => enums::expand_easy_plugin_enum(context, span, arguments),
            "struct" => structs::expand_easy_plugin_struct(context, span, arguments),
            _ => arguments[0].to_error("expected `enum` or `struct`"),
        },
        _ => arguments[0].to_error("expected `enum` or `struct`"),
    }
}

#[doc(hidden)]
pub fn expand_easy_plugin(
    context: &mut ExtCtxt, span: Span, arguments: &[TokenTree]
) -> Box<MacResult + 'static> {
    match expand_easy_plugin_(context, span, arguments) {
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
    registry.register_macro("parse_spec", expand_parse_spec);
    registry.register_macro("easy_plugin", expand_easy_plugin);
}
