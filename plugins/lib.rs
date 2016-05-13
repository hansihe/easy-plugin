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

// Conversion ____________________________________

/// Indicates the requested conversion for a enum variant field.
#[derive(Copy, Clone, Debug)]
enum Conversion {
    Clone,
    ToString,
    AsStrToString,
    MapAsStrToString,
}

impl Conversion {
    //- Constructors -----------------------------

    fn from_specifier(specifier: &str) -> Conversion {
        match specifier {
            "ts" => Conversion::ToString,
            "asts" => Conversion::AsStrToString,
            "masts" => Conversion::MapAsStrToString,
            _ => Conversion::Clone,
        }
    }

    //- Accessors --------------------------------

    fn to_expr(self, context: &mut ExtCtxt, ident: Ident) -> P<Expr> {
        match self {
            Conversion::Clone => quote_expr!(context, $ident.clone()),
            Conversion::ToString => quote_expr!(context, $ident.to_string()),
            Conversion::AsStrToString => quote_expr!(context, $ident.as_str().to_string()),
            Conversion::MapAsStrToString =>
                quote_expr!(context, $ident.map(|v| v.as_str().to_string())),
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

fn expand_convert_fn_doc(
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

fn expand_convert_fn(
    context: &mut ExtCtxt,
    span: Span,
    arguments: &[TokenTree],
    pname: Ident,
    pty: &P<Ty>,
    pexpr: &P<Expr>,
    dname: Ident,
) -> P<Item> {
    let dvariant = to_ident(&arguments[0]);
    let dfields = to_delimited(&arguments[1]);
    let rty = parse_ty(context, &arguments[3..4]);

    let doc = expand_convert_fn_doc(context, span, pty, dname, dvariant, dfields.tts.len());
    let name = context.ident_of(&format!("{}_to_{}", pname, camel_case_to_snake_case(dvariant)));

    let fields = dfields.tts.iter().filter_map(|tt| {
        match tt {
            &TokenTree::Token(_, Token::Underscore) => Some("_".into()),
            &TokenTree::Token(_, Token::Ident(ref ident)) => Some(ident.name.as_str().to_string()),
            _ => None,
        }
    }).enumerate().map(|(i, s)| {
        let mut buffer = String::new();
        buffer.push(((97 + i) as u8) as char);
        (Conversion::from_specifier(&s), context.ident_of(&buffer))
    }).collect::<Vec<_>>();

    let path = context.path_all(span, false, vec![dname, dvariant], vec![], vec![], vec![]);
    let pats = fields.iter().cloned().map(|(_, p)| quote_pat!(context, ref $p)).collect();
    let pat = context.pat_enum(span, path, pats);
    let mut exprs = fields.into_iter().map(|(c, p)| c.to_expr(context, p)).collect::<Vec<_>>();
    let expr = if exprs.len() == 1 {
        exprs.remove(0)
    } else {
        context.expr_tuple(span, exprs)
    };

    let message = get_lit_str(span, &format!("expected `{}::{}` {}", dname, dvariant, pname));
    let span = if pname.name.as_str() == "tt" {
        quote_expr!(context, $pname.get_span())
    } else {
        quote_expr!(context, $pname.span)
    };

    quote_item!(context,
        #[$doc]
        pub fn $name($pname: &$pty) -> PluginResult<$rty> {
            match $pexpr {
                $pat => Ok($expr),
                _ => Err(($span, $message.into())),
            }
        }
    ).unwrap()
}

fn expand_convert(
    context: &mut ExtCtxt, span: Span, arguments: &[TokenTree]
) -> Box<MacResult + 'static> {
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

    assert_eq!(dconverters.tts.len() % 5, 0);
    let items = dconverters.tts.chunks(5).map(|c| {
        expand_convert_fn(context, span, c, pname, &pty, &pexpr, dname)
    }).collect();
    MacEager::items(SmallVector::many(items))
}

#[doc(hidden)]
#[plugin_registrar]
pub fn plugin_registrar(registry: &mut Registry) {
    registry.register_macro("convert", expand_convert);
}
