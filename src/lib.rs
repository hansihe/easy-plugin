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
//! | Name    | Description                           |  Storage Type            |
//! |:--------|:--------------------------------------|:-------------------------|
//! | `attr`  | An attribute                          | `Attribute`              |
//! | `binop` | A binary operator                     | `Spanned<BinOpToken>`    |
//! | `block` | A brace-delimited statement sequence  | `P<Block>`               |
//! | `delim` | A delimited token tree sequence       | `Spanned<Rc<Delimited>>` |
//! | `expr`  | An expression                         | `P<Expr>`                |
//! | `ident` | An identifier                         | `Spanned<Ident>`         |
//! | `item`  | An item                               | `P<Item>`                |
//! | `lftm`  | A lifetime                            | `Spanned<Name>`          |
//! | `lit`   | A literal                             | `Lit`                    |
//! | `meta`  | A "meta" item, as found in attributes | `P<MetaItem>`            |
//! | `pat`   | A pattern                             | `P<Pat>`                 |
//! | `path`  | A qualified name                      | `Spanned<Path>`          |
//! | `stmt`  | A single statement                    | `P<Stmt>`                |
//! | `ty`    | A type                                | `P<Ty>`                  |
//! | `tok`   | A single token                        | `Spanned<Token>`         |
//! | `tt`    | A single token tree                   | `TokenTree`              |
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

#![feature(plugin_registrar, quote, rustc_private)]

#![warn(missing_copy_implementations, missing_debug_implementations, missing_docs)]

#![cfg_attr(feature="clippy", feature(plugin))]
#![cfg_attr(feature="clippy", plugin(clippy))]
#![cfg_attr(feature="clippy", warn(clippy))]
#![cfg_attr(feature="clippy", allow(similar_names, used_underscore_binding))]

extern crate rustc_plugin;
extern crate syntax;

use rustc_plugin::{Registry};

use syntax::ast::*;
use syntax::codemap::{Span};
use syntax::ext::base::{ExtCtxt, DummyResult, MacEager, MacResult};
use syntax::ext::build::{AstBuilder};
use syntax::parse::token::{DelimToken, Token};
use syntax::ptr::{P};
use syntax::util::small_vector::{SmallVector};

mod utility;
use utility::{ToError, ToExpr};

mod arguments;
pub use self::arguments::*;

#[macro_use]
mod specification;
pub use self::specification::*;

/// A result type suitable for reporting errors in plugins.
pub type PluginResult<T> = Result<T, (Span, String)>;

//================================================
// Functions
//================================================

fn strip_function(
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

fn expand_struct(
    context: &mut ExtCtxt, span: Span, name: Ident, specification: &Specification
) -> P<Item> {
    let fields = specification.iter().flat_map(|s| {
        s.to_struct_fields(context, span).into_iter()
    }).collect::<Vec<_>>();
    let struct_ = if fields.is_empty() {
        quote_item!(context, struct $name;).unwrap()
    } else {
        context.item_struct(span, name, VariantData::Struct(fields, DUMMY_NODE_ID))
    };
    struct_.map(|mut s| {
        s.attrs = vec![quote_attr!(context, #[derive(Clone, Debug)])];
        s
    })
}

fn expand_structs(
    context: &mut ExtCtxt, span: Span, specifications: &[(Ident, Specification)]
) -> Vec<P<Item>> {
    specifications.iter().map(|&(n, ref s)| expand_struct(context, span, n, s)).collect()
}

fn expand_parse(
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
    quote_item!(context,
        #[allow(non_snake_case)]
        fn $function(
            session: &::syntax::parse::ParseSess, arguments: &[::syntax::ast::TokenTree]
        ) -> ::easy_plugin::PluginResult<$name> {
            ::easy_plugin::parse_arguments(session, arguments, &$specification.0).map(|_m| $result)
        }
    ).unwrap()
}

fn expand_parses(
    context: &mut ExtCtxt, span: Span, specifications: &[(Ident, Specification)]
) -> Vec<P<Item>> {
    specifications.iter().map(|&(n, ref s)| expand_parse(context, span, n, s, true)).collect()
}

fn expand_enum_easy_plugin_(
    context: &mut ExtCtxt,
    span: Span,
    arguments: Ident,
    names: Vec<Ident>,
    ttss: Vec<Vec<TokenTree>>,
    function: P<Item>,
) -> PluginResult<Box<MacResult + 'static>> {
    let specifications: Result<Vec<_>, _> = names.iter().zip(ttss.into_iter()).map(|(n, tts)| {
        parse_specification(&tts).map(|s| (*n, s))
    }).collect();
    let specifications = try!(specifications);
    let structs = expand_structs(context, span, &specifications);
    let parses = expand_parses(context, span, &specifications);

    let (function, identifier, visibility, attributes) = strip_function(context, function);
    let inner = function.ident;
    let stmts = names.iter().enumerate().map(|(i, ref n)| {
        let parse = context.ident_of(&format!("parse{}", n));
        if i + 1 < specifications.len() {
            quote_stmt!(context,
                if let Ok(arguments) = $parse(context.parse_sess, arguments) {
                    return match $inner(context, span, $arguments::$n(arguments)) {
                        Ok(result) => result,
                        Err((subspan, message)) => {
                            let span = if subspan == ::syntax::codemap::DUMMY_SP {
                                span
                            } else {
                                subspan
                            };

                            context.span_err(span, &message);
                            ::syntax::ext::base::DummyResult::any(span)
                        }
                    };
                }
            )
        } else {
            quote_stmt!(context,
                return match $parse(context.parse_sess, arguments).and_then(|a| {
                    $inner(context, span, $arguments::$n(a))
                }) {
                    Ok(result) => result,
                    Err((subspan, message)) => {
                        let span = if subspan == ::syntax::codemap::DUMMY_SP {
                            span
                        } else {
                            subspan
                        };

                        context.span_err(span, &message);
                        ::syntax::ext::base::DummyResult::any(span)
                    }
                };
            )
        }
    }).collect::<Vec<_>>();

    let variants = names.iter().map(|n| {
        context.variant(span, *n, vec![quote_ty!(context, $n)])
    }).collect();
    let enum_ = context.item_enum(span, arguments, EnumDef { variants: variants }).map(|mut e| {
        e.attrs = vec![quote_attr!(context, #[derive(Clone, Debug)])];
        e
    });

    let item = quote_item!(context,
        fn $identifier(
            context: &mut ::syntax::ext::base::ExtCtxt,
            span: ::syntax::codemap::Span,
            arguments: &[::syntax::ast::TokenTree],
        ) -> ::std::boxed::Box<::syntax::ext::base::MacResult> {
            $structs
            $enum_
            $parses
            $function
            $stmts
        }
    ).unwrap().map(|mut i| {
        i.vis = visibility;
        i.attrs = attributes;
        i
    });
    Ok(MacEager::items(SmallVector::one(item)))
}

fn expand_enum_easy_plugin(
    context: &mut ExtCtxt, span: Span, arguments: &[TokenTree]
) -> PluginResult<Box<MacResult + 'static>> {
    let specification = &[
        Specifier::specific_ident("enum"),
        Specifier::Ident("arguments".into()),
        Specifier::Delimited(DelimToken::Brace, spec![
            Specifier::Sequence(Amount::ZeroOrMore, None, spec![
                Specifier::Ident("name".into()),
                Specifier::Delimited(DelimToken::Brace, spec![
                    Specifier::Sequence(Amount::ZeroOrMore, None, spec![
                        Specifier::Tt("tt".into()),
                    ]),
                ]),
                Specifier::Specific(Token::Comma),
            ]),
        ]),
        Specifier::Item("function".into()),
    ];
    let matches = try!(parse_arguments(context.parse_sess, arguments, specification));
    let arguments = matches.get("arguments").unwrap().as_ident().node;
    let names = matches.get("name").unwrap().as_sequence().into_iter().map(|s| {
        s.as_ident().node
    }).collect();
    let ttss = matches.get("tt").unwrap().as_sequence().into_iter().map(|s| {
        s.as_sequence().into_iter().map(|s| s.as_tt()).collect::<Vec<_>>()
    }).collect();
    let function = matches.get("function").unwrap().as_item();
    expand_enum_easy_plugin_(context, span, arguments, names, ttss, function)
}

fn expand_struct_easy_plugin_(
    context: &mut ExtCtxt, span: Span, arguments: Ident, tts: Vec<TokenTree>, function: P<Item>
) -> PluginResult<Box<MacResult + 'static>> {
    let specification = try!(parse_specification(&tts));
    let struct_ = expand_struct(context, span, arguments, &specification);
    let parse = expand_parse(context, span, arguments, &specification, false);
    let (function, identifier, visibility, attributes) = strip_function(context, function);
    let inner = function.ident;
    let item = quote_item!(context,
        fn $identifier(
            context: &mut ::syntax::ext::base::ExtCtxt,
            span: ::syntax::codemap::Span,
            arguments: &[::syntax::ast::TokenTree],
        ) -> ::std::boxed::Box<::syntax::ext::base::MacResult> {
            $struct_
            $parse
            $function
            match parse(context.parse_sess, arguments).and_then(|a| $inner(context, span, a)) {
                Ok(result) => result,
                Err((subspan, message)) => {
                    let span = if subspan == ::syntax::codemap::DUMMY_SP {
                        span
                    } else {
                        subspan
                    };

                    context.span_err(span, &message);
                    ::syntax::ext::base::DummyResult::any(span)
                },
            }
        }
    ).unwrap().map(|mut i| {
        i.vis = visibility;
        i.attrs = attributes;
        i
    });
    Ok(MacEager::items(SmallVector::one(item)))
}

fn expand_struct_easy_plugin(
    context: &mut ExtCtxt, span: Span, arguments: &[TokenTree]
) -> PluginResult<Box<MacResult + 'static>> {
    let specification = &[
        Specifier::specific_ident("struct"),
        Specifier::Ident("arguments".into()),
        Specifier::Delimited(DelimToken::Brace, spec![
            Specifier::Sequence(Amount::ZeroOrMore, None, spec![
                Specifier::Tt("tt".into()),
            ]),
        ]),
        Specifier::Item("function".into()),
    ];
    let matches = try!(parse_arguments(context.parse_sess, arguments, specification));
    let arguments = matches.get("arguments").unwrap().as_ident().node;
    let tts = matches.get("tt").unwrap().as_sequence().iter().map(|s| {
        s.as_tt()
    }).collect::<Vec<_>>();
    let function = matches.get("function").unwrap().as_item();
    expand_struct_easy_plugin_(context, span, arguments, tts, function)
}

fn expand_easy_plugin_(
    context: &mut ExtCtxt, span: Span, arguments: &[TokenTree]
) -> PluginResult<Box<MacResult + 'static>> {
    if arguments.is_empty() {
        return span.to_error("unexpected end of arguments");
    }
    match arguments[0] {
        TokenTree::Token(_, Token::Ident(ref ident)) => match &*ident.name.as_str() {
            "enum" => expand_enum_easy_plugin(context, span, arguments),
            "struct" => expand_struct_easy_plugin(context, span, arguments),
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
    registry.register_macro("parse_specification", expand_parse_specification);
    registry.register_macro("easy_plugin", expand_easy_plugin);
}
