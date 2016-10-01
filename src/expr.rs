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

use syntax::ast::{Expr, Ident};
use syntax::codemap::{Span};
use syntax::ext::base::{ExtCtxt};
use syntax::ext::build::{AstBuilder};
use syntax::parse::token::{DelimToken, Token};
use syntax::ptr::{P};

use synthax;

use super::*;

//================================================
// Macros
//================================================

// struct_expr! __________________________________

macro_rules! struct_expr {
    ($context:expr, $span:expr, $struct_:expr, $name:ident, [$($field:ident), +]) => ({
        let path = mk_idents($context, &["easy_plugin", stringify!($name)]);
        let fields = vec![
            $($context.field_imm(
                $span,
                $context.ident_of(stringify!($field)),
                $struct_.$field.to_expr($context, $span),
            )), +
        ];
        $context.expr_struct($span, $context.path_global($span, path), fields)
    });
}

//================================================
// Traits
//================================================

// ToExpr ________________________________________

pub trait ToExpr {
    fn to_expr(&self, context: &ExtCtxt, span: Span) -> P<Expr>;
}

impl<T: ToExpr> ToExpr for Box<T> {
    fn to_expr(&self, context: &ExtCtxt, span: Span) -> P<Expr> {
        let idents = mk_idents(context, &["std", "boxed", "Box", "new"]);
        context.expr_call_global(span, idents, vec![(&*self as &T).to_expr(context, span)])
    }
}

impl<T: ToExpr> ToExpr for Option<T> {
    fn to_expr(&self, context: &ExtCtxt, span: Span) -> P<Expr> {
        match *self {
            Some(ref some) => context.expr_some(span, some.to_expr(context, span)),
            None => context.expr_none(span),
        }
    }
}

impl<T: ToExpr> ToExpr for Vec<T> {
    fn to_expr(&self, context: &ExtCtxt, span: Span) -> P<Expr> {
        let exprs = self.iter().map(|e| e.to_expr(context, span)).collect();
        let vec = context.expr_vec(span, exprs);
        context.expr_method_call(span, vec, context.ident_of("to_vec"), vec![])
    }
}

impl ToExpr for Amount {
    fn to_expr(&self, context: &ExtCtxt, span: Span) -> P<Expr> {
        let idents = mk_idents(context, &["easy_plugin", "Amount", &format!("{:?}", self)]);
        context.expr_path(context.path_global(span, idents))
    }
}

impl ToExpr for Delimited {
    fn to_expr(&self, context: &ExtCtxt, span: Span) -> P<Expr> {
        struct_expr!(context, span, self, Delimited, [delimiter, specification])
    }
}

impl ToExpr for DelimToken {
    fn to_expr(&self, context: &ExtCtxt, span: Span) -> P<Expr> {
        synthax::ToExpr::to_expr(self, context, span)
    }
}

impl ToExpr for Enum {
    fn to_expr(&self, context: &ExtCtxt, span: Span) -> P<Expr> {
        struct_expr!(context, span, self, Enum, [name, variants])
    }
}

impl ToExpr for Extractor {
    fn to_expr(&self, context: &ExtCtxt, span: Span) -> P<Expr> {
        struct_expr!(context, span, self, Extractor, [specifier, extractor])
    }
}

impl ToExpr for Sequence {
    fn to_expr(&self, context: &ExtCtxt, span: Span) -> P<Expr> {
        struct_expr!(context, span, self, Sequence, [amount, separator, specification])
    }
}

impl ToExpr for Specification {
    fn to_expr(&self, context: &ExtCtxt, span: Span) -> P<Expr> {
        let (variant, arguments) = match *self {
            Specification::Enum(ref enum_) => ("Enum", vec![enum_.to_expr(context, span)]),
            Specification::Struct(ref struct_) => ("Struct", vec![struct_.to_expr(context, span)]),
        };
        let idents = mk_idents(context, &["easy_plugin", "Specification", variant]);
        context.expr_call_global(span, idents, arguments)
    }
}

impl ToExpr for Specifier {
    fn to_expr(&self, context: &ExtCtxt, span: Span) -> P<Expr> {
        macro_rules! exprs {
            ($($expr:expr), +) => ({
                vec![$($expr.to_expr(context, span)), +]
            });
        }

        let (variant, arguments) = match *self {
            Specifier::Attr(ref name) => ("Attr", exprs![name]),
            Specifier::BinOp(ref name) => ("BinOp", exprs![name]),
            Specifier::Block(ref name) => ("Block", exprs![name]),
            Specifier::Delim(ref name) => ("Delim", exprs![name]),
            Specifier::Expr(ref name) => ("Expr", exprs![name]),
            Specifier::Ident(ref name) => ("Ident", exprs![name]),
            Specifier::Item(ref name) => ("Item", exprs![name]),
            Specifier::Lftm(ref name) => ("Lftm", exprs![name]),
            Specifier::Lit(ref name) => ("Lit", exprs![name]),
            Specifier::Meta(ref name) => ("Meta", exprs![name]),
            Specifier::Pat(ref name) => ("Pat", exprs![name]),
            Specifier::Path(ref name) => ("Path", exprs![name]),
            Specifier::Stmt(ref name) => ("Stmt", exprs![name]),
            Specifier::Ty(ref name) => ("Ty", exprs![name]),
            Specifier::Tok(ref name) => ("Tok", exprs![name]),
            Specifier::Tt(ref name) => ("Tt", exprs![name]),
            Specifier::Extractor(ref name, ref value) => ("Extractor", exprs![name, value]),
            Specifier::Specific(ref value) => ("Specific", exprs![value]),
            Specifier::Delimited(ref value) => ("Delimited", exprs![value]),
            Specifier::Sequence(ref name, ref value) => ("Sequence", exprs![name, value]),
            Specifier::Enum(ref name, ref value) => ("Enum", exprs![name, value]),
            Specifier::Struct(ref name, ref value) => ("Struct", exprs![name, value]),
        };
        let idents = mk_idents(context, &["easy_plugin", "Specifier", variant]);
        context.expr_call_global(span, idents, arguments)
    }
}

impl ToExpr for String {
    fn to_expr(&self, context: &ExtCtxt, span: Span) -> P<Expr> {
        synthax::ToExpr::to_expr(self, context, span)
    }
}

impl ToExpr for Struct {
    fn to_expr(&self, context: &ExtCtxt, span: Span) -> P<Expr> {
        struct_expr!(context, span, self, Struct, [name, specification])
    }
}

impl ToExpr for Token {
    fn to_expr(&self, context: &ExtCtxt, span: Span) -> P<Expr> {
        synthax::ToExpr::to_expr(self, context, span)
    }
}

impl ToExpr for Variant {
    fn to_expr(&self, context: &ExtCtxt, span: Span) -> P<Expr> {
        struct_expr!(context, span, self, Variant, [name, specification])
    }
}

//================================================
// Functions
//================================================

fn mk_idents(context: &ExtCtxt, idents: &[&str]) -> Vec<Ident> {
    idents.iter().map(|i| context.ident_of(i)).collect()
}
