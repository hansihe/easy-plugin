//! Plugins used internally by `easy-plugin`.

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

#[derive(Copy, Clone, Debug)]
enum Conversion {
    Clone,
    ToString,
    AsStrToString,
    MapAsStrToString,
}

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

fn to_snake_case(ident: Ident) -> String {
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

#[doc(hidden)]
pub fn expand_convert(
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

    let items = to_delimited(&arguments[7]).tts.chunks(5).map(|c| {
        let dvariant = to_ident(&c[0]);
        let dfields = to_delimited(&c[1]);
        let rty = parse_ty(context, &c[3..4]);

        let ty = pprust::ty_to_string(&pty);
        let doc = if dfields.tts.len() < 2 {
            format!("Returns the `{}::{}` value in the supplied `{}`.", dname, dvariant, ty)
        } else {
            format!("Returns the `{}::{}` values in the supplied `{}`.", dname, dvariant, ty)
        };
        let doc = get_doc_comment(context, span, &doc);
        let name = context.ident_of(&format!("{}_to_{}", pname, to_snake_case(dvariant)));
        let msg = get_lit_str(span, &format!("expected {}::{} {}", dname, dvariant, pname));
        let mut character: u8 = 97;
        let fields = dfields.tts.iter().filter_map(|tt| {
            let conversion = match tt {
                &TokenTree::Token(_, Token::Underscore) => Conversion::Clone,
                &TokenTree::Token(_, Token::Ident(ref ident)) => match &*ident.name.as_str() {
                    "ts" => Conversion::ToString,
                    "asts" => Conversion::AsStrToString,
                    "masts" => Conversion::MapAsStrToString,
                    _ => unreachable!(),
                },
                _ => return None,
            };
            let mut string = String::new();
            string.push(character as char);
            let field = (conversion, context.ident_of(&string));
            character += 1;
            Some(field)
        }).collect::<Vec<_>>();
        let path = context.path_all(span, false, vec![dname, dvariant], vec![], vec![], vec![]);
        let pats = fields.iter().cloned().map(|(_, p)| quote_pat!(context, ref $p)).collect();
        let pat = context.pat_enum(span, path, pats);
        let mut exprs = fields.into_iter().map(|(c, p)| {
            match c {
                Conversion::Clone => quote_expr!(context, $p.clone()),
                Conversion::ToString => quote_expr!(context, $p.to_string()),
                Conversion::AsStrToString => quote_expr!(context, $p.as_str().to_string()),
                Conversion::MapAsStrToString => quote_expr!(context, $p.map(|p| p.as_str().to_string())),
            }
        }).collect::<Vec<_>>();
        let expr = if exprs.len() == 1 {
            exprs.remove(0)
        } else {
            context.expr_tuple(span, exprs)
        };
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
                    _ => Err(($span, $msg.into())),
                }
            }
        ).unwrap()
    }).collect();
    MacEager::items(SmallVector::many(items))
}

#[doc(hidden)]
#[plugin_registrar]
pub fn plugin_registrar(registry: &mut Registry) {
    registry.register_macro("convert", expand_convert);
}
