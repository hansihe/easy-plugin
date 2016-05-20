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

#![feature(plugin_registrar, quote, rustc_private)]

extern crate rustc_plugin;
extern crate syntax;

use std::rc::{Rc};

use rustc_plugin::{Registry};

use syntax::print::pprust;
use syntax::ast::*;
use syntax::codemap::{self, Span};
use syntax::ext::base::{ExtCtxt, MacEager, MacResult};
use syntax::ext::build::{AstBuilder};
use syntax::parse::token::{self, Token};
use syntax::ptr::{P};
use syntax::util::small_vector::{SmallVector};

//================================================
// Enums
//================================================

// Call __________________________________________

/// Indicates the methods to be called on a value to return it from a converter function.
#[derive(Copy, Clone, Debug)]
enum Call {
    Clone,
    ToString,
    AsStrToString,
    MapAsStrToString,
}

impl Call {
    //- Constructors -----------------------------

    fn from_specifier(specifier: &str) -> Call {
        match specifier {
            "ts" => Call::ToString,
            "asts" => Call::AsStrToString,
            "masts" => Call::MapAsStrToString,
            _ => Call::Clone,
        }
    }

    //- Accessors --------------------------------

    fn to_expr(self, context: &mut ExtCtxt, ident: Ident) -> P<Expr> {
        match self {
            Call::Clone => quote_expr!(context, $ident.clone()),
            Call::ToString => quote_expr!(context, $ident.to_string()),
            Call::AsStrToString => quote_expr!(context, $ident.as_str().to_string()),
            Call::MapAsStrToString => quote_expr!(context, $ident.map(|f| f.as_str().to_string())),
        }
    }
}

//================================================
// Functions
//================================================

fn get_doc_comment(context: &mut ExtCtxt, span: Span, value: &str) -> P<MetaItem> {
    let value = LitKind::Str(token::intern_and_get_ident(value), StrStyle::Cooked);
    context.meta_name_value(span, token::intern_and_get_ident("doc"), value)
}

fn get_lit_str(span: Span, value: &str) -> Lit {
    codemap::respan(span, LitKind::Str(token::intern_and_get_ident(value), StrStyle::Cooked))
}

fn parse_expr(context: &mut ExtCtxt, tts: &[TokenTree]) -> P<Expr> {
    context.new_parser_from_tts(tts).parse_expr().unwrap()
}

fn parse_ty(context: &mut ExtCtxt, tts: &[TokenTree]) -> P<Ty> {
    context.new_parser_from_tts(tts).parse_ty().unwrap()
}

fn to_delimited(tt: &TokenTree) -> Rc<Delimited> {
    match tt {
        &TokenTree::Delimited(_, ref delimited) => delimited.clone(),
        _ => unreachable!(),
    }
}

fn to_ident(tt: &TokenTree) -> Ident {
    match tt {
        &TokenTree::Token(_, Token::Ident(ref name)) => name.clone(),
        _ => unreachable!(),
    }
}

fn camel_case_to_snake_case(ident: Ident) -> String {
    let mut snake = String::new();
    for c in ident.name.as_str().chars() {
        if c.is_uppercase() {
            if !snake.is_empty() {
                snake.push('_');
            }
            snake.extend(c.to_lowercase());
        } else {
            snake.push(c);
        }
    }
    snake
}

/// Returns a doc comment meta item with appropriate documentation for a converter function.
fn expand_convert_fn_doc_comment(
    context: &mut ExtCtxt, span: Span, pty: &P<Ty>, dname: Ident, dvariant: Ident, fields: usize
) -> P<MetaItem> {
    let ty = pprust::ty_to_string(&pty);
    let doc = match fields {
        0 => format!("Returns `Ok` if the supplied `{}` is `{}::{}`", ty, dname, dvariant),
        1 => format!("Returns the `{}::{}` value in the supplied `{}`.", dname, dvariant, ty),
        _ => format!("Returns the `{}::{}` values in the supplied `{}`.", dname, dvariant, ty),
    };
    get_doc_comment(context, span, &doc)
}

/// Returns a converter function item.
fn expand_convert_fn(
    context: &mut ExtCtxt,
    span: Span,
    arguments: &[TokenTree],
    pname: Ident,
    pty: &P<Ty>,
    pexpr: &P<Expr>,
    dname: Ident,
) -> P<Item> {
    // Validate and extract the arguments.
    let dvariant = to_ident(&arguments[0]);
    let dfields = to_delimited(&arguments[1]);
    let rty = parse_ty(context, &arguments[3..4]);

    // Build the documentation.
    let doc = expand_convert_fn_doc_comment(context, span, pty, dname, dvariant, dfields.tts.len());

    // Build the name.
    let name = context.ident_of(&format!("{}_to_{}", pname, camel_case_to_snake_case(dvariant)));

    // Determine the variant field names and required method calls to return them.
    let fields = dfields.tts.iter().filter_map(|tt| {
        match tt {
            &TokenTree::Token(_, Token::Underscore) => Some("_".into()),
            &TokenTree::Token(_, Token::Ident(ref ident)) => Some(ident.name.as_str().to_string()),
            _ => None,
        }
    }).enumerate().map(|(i, s)| {
        let mut buffer = String::new();
        buffer.push(((97 + i) as u8) as char);
        (Call::from_specifier(&s), context.ident_of(&buffer))
    }).collect::<Vec<_>>();

    // Build the variant pat.
    let path = context.path_all(span, false, vec![dname, dvariant], vec![], vec![], vec![]);
    let pats = fields.iter().cloned().map(|(_, p)| quote_pat!(context, ref $p)).collect();
    let pat = context.pat_enum(span, path, pats);

    // Build the expr that returns the variant fields.
    let mut exprs = fields.into_iter().map(|(c, p)| c.to_expr(context, p)).collect::<Vec<_>>();
    let expr = if exprs.len() == 1 {
        exprs.remove(0)
    } else {
        context.expr_tuple(span, exprs)
    };

    // Build the error message.
    let message = get_lit_str(span, &format!("expected `{}::{}` {}", dname, dvariant, pname));

    // Build the converter function item.
    quote_item!(context,
        #[$doc]
        pub fn $name($pname: &$pty) -> PluginResult<$rty> {
            match $pexpr {
                $pat => Ok($expr),
                _ => $pname.to_error($message),
            }
        }
    ).unwrap()
}

/// Returns converter function items.
///
/// A converter function attempts to extract the values in the `node` of an AST element. For
/// example, `expr_to_vec` takes an `&Expr` and returns a `PluginResult<Vec<P<Expr>>>`. If the
/// `node` in the supplied `&Expr` is the `ExprKind::Vec` variant, the value contained in the
/// variant is returned as an `Ok` value. Otherwise, an `Err` value is returned.
fn expand_convert(
    context: &mut ExtCtxt, span: Span, arguments: &[TokenTree]
) -> Box<MacResult + 'static> {
    // Validate and extract the arguments.
    assert_eq!(arguments.len(), 8);
    let pname = to_ident(&arguments[0]);
    let pty = match &arguments[2] {
        &TokenTree::Delimited(_, ref delimited) => delimited.tts.clone(),
        tt @ _ => vec![tt.clone()],
    };
    let pty = parse_ty(context, &pty[..]);
    let pexpr = parse_expr(context, &to_delimited(&arguments[3]).tts[..]);
    let dname = to_ident(&arguments[5]);
    let dconverters = to_delimited(&arguments[7]);

    // Expand the list of converter specifications into converter function items.
    assert_eq!(dconverters.tts.len() % 5, 0);
    let items = dconverters.tts.chunks(5).map(|c| {
        expand_convert_fn(context, span, c, pname, &pty, &pexpr, dname)
    }).collect();
    MacEager::items(SmallVector::many(items))
}

#[doc(hidden)]
#[plugin_registrar]
pub fn plugin_registrar(registry: &mut Registry) {
    registry.register_macro("__easy_plugin_convert", expand_convert);
}
