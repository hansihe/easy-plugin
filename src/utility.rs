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

use std::cell::{RefCell};
use std::marker::{PhantomData};

use syntax::ext::tt::transcribe;
use syntax::parse::token;
use syntax::ast::*;
use syntax::codemap::{DUMMY_SP, MultiSpan, Span};
use syntax::errors::{FatalError, Level, RenderSpan};
use syntax::errors::emitter::{Emitter};
use syntax::ext::base::{ExtCtxt};
use syntax::ext::build::{AstBuilder};
use syntax::parse::{ParseSess, PResult};
use syntax::parse::lexer::{Reader, TokenAndSpan};
use syntax::parse::parser::{Parser, PathParsingMode};
use syntax::parse::token::{BinOpToken, DelimToken, IdentStyle, Token};
use syntax::ptr::{P};

use super::{PluginResult};

//================================================
// Macros
//================================================

// parse! _______________________________________

/// Defines a parsing method for `TransactionParser`.
macro_rules! parse {
    ($name:ident($($argument:expr), *)$(.$method:ident())*, $description:expr, $ty:ty) => {
        pub fn $name(&mut self, name: &str) -> PluginResult<$ty> {
            self.parse2($description, name, |p| p.$name($($argument), *))
        }
    };

    (OPTION: $name:ident($($argument:expr), *)$(.$method:ident())*, $description:expr, $ty:ty) => {
        pub fn $name(&mut self, name: &str) -> PluginResult<$ty> {
            match self.apply(|p| p.$name($($argument), *)) {
                Ok(Some(value)) => return Ok(value),
                Err(mut db) => db.cancel(),
                _ => { },
            }

            self.get_last_span().to_error(format!("expected {}: '{}'", $description, name))
        }
    };
}

// token! ________________________________________

/// Prefixes a list of identifiers with `syntax`, `parse`, and `token`.
macro_rules! token {
    ($($ident:expr), +) => (&["syntax", "parse", "token", $($ident), *]);
}

//================================================
// Traits
//================================================

// ToError _______________________________________

/// A type that can be converted into a `PluginResult<T>`.
pub trait ToError<T, S> where S: AsRef<str> {
    /// Returns an `Err` value with the span of this value and the supplied message.
    fn to_error(&self, message: S) -> PluginResult<T>;
}

impl<T, S: AsRef<str>> ToError<T, S> for Span {
    fn to_error(&self, message: S) -> PluginResult<T> {
        Err((*self, message.as_ref().into()))
    }
}

impl<T, S: AsRef<str>> ToError<T, S> for TokenTree {
    fn to_error(&self, message: S) -> PluginResult<T> {
        Err((self.get_span(), message.as_ref().into()))
    }
}

// ToExpr ________________________________________

/// A type that can be converted into a `P<Expr>`.
pub trait ToExpr {
    /// Returns a `P<Expr>` which would produce this value if executed.
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr>;
}

impl ToExpr for BinOpToken {
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        mk_expr_path(context, span, token!["BinOpToken", &format!("{:?}", self)])
    }
}

impl ToExpr for DelimToken {
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        mk_expr_path(context, span, token!["DelimToken", &format!("{:?}", self)])
    }
}

impl ToExpr for Ident {
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        let arguments = vec![context.expr_str(span, self.name.as_str())];
        mk_expr_call(context, span, token!["str_to_ident"], arguments)
    }
}

impl ToExpr for IdentStyle {
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        mk_expr_path(context, span, token!["IdentStyle", &format!("{:?}", self)])
    }
}

impl ToExpr for token::Lit {
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        macro_rules! expr {
            ($variant:expr, $name:expr) => ({
                let arguments = vec![$name.to_expr(context, span)];
                mk_expr_call(context, span, token!["Lit", $variant], arguments)
            });

            ($variant:expr, $name:expr, $size:expr) => ({
                let arguments = vec![$name.to_expr(context, span), context.expr_usize(span, $size)];
                mk_expr_call(context, span, token!["Lit", $variant], arguments)
            });
        }

        match *self {
            token::Lit::Byte(name) => expr!("Byte", name),
            token::Lit::Char(name) => expr!("Char", name),
            token::Lit::Integer(name) => expr!("Integer", name),
            token::Lit::Float(name) => expr!("Float", name),
            token::Lit::Str_(name) => expr!("Str_", name),
            token::Lit::StrRaw(name, size) => expr!("StrRaw", name, size),
            token::Lit::ByteStr(name) => expr!("ByteStr", name),
            token::Lit::ByteStrRaw(name, size) => expr!("ByteStrRaw", name, size),
        }
    }
}

impl ToExpr for Name {
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        mk_expr_call(context, span, token!["intern"], vec![context.expr_str(span, self.as_str())])
    }
}

impl ToExpr for String {
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        let name = context.expr_str(span, context.name_of(self).as_str());
        let into = context.ident_of("into");
        context.expr_method_call(span, name, into, vec![])
    }
}

impl ToExpr for Token {
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        macro_rules! expr {
            ($variant:expr, $($argument:expr), *) => ({
                let arguments = vec![$($argument.to_expr(context, span)), *];
                mk_expr_call(context, span, token!["Token", $variant], arguments)
            });
        }

        match *self {
            Token::BinOp(binop) => expr!("BinOp", binop),
            Token::BinOpEq(binop) => expr!("BinOpEq", binop),
            Token::Literal(lit, suffix) => expr!("Literal", lit, suffix),
            Token::Ident(ref ident, style) => expr!("Ident", ident, style),
            Token::Lifetime(ref lifetime) => expr!("Lifetime", lifetime),
            Token::DocComment(comment) => expr!("DocComment", comment),
            Token::OpenDelim(_) |
            Token::CloseDelim(_) |
            Token::Shebang(_) |
            Token::Interpolated(_) |
            Token::MatchNt(_, _, _, _) |
            Token::SubstNt(_, _) |
            Token::SpecialVarNt(_) => unreachable!(),
            _ => mk_expr_path(context, span, token!["Token", &format!("{:?}", self)]),
        }
    }
}

impl<T> ToExpr for Option<T> where T: ToExpr {
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        match *self {
            Some(ref some) => {
                let some = some.to_expr(context, span);
                context.expr_some(span, some)
            },
            None => context.expr_none(span),
        }
    }
}

impl<T> ToExpr for Vec<T> where T: ToExpr {
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        let exprs = self.iter().map(|i| i.to_expr(context, span)).collect();
        let slice = context.expr_vec_slice(span, exprs);
        context.expr_method_call(span, slice, context.ident_of("to_vec"), vec![])
    }
}

impl<T> ToExpr for [T] where T: ToExpr {
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        let exprs = self.iter().map(|i| i.to_expr(context, span)).collect();
        context.expr_vec_slice(span, exprs)
    }
}

//================================================
// Structs
//================================================

// SaveEmitter ___________________________________

/// The most recent fatal message.
thread_local! { static ERROR: RefCell<Option<(Span, String)>> = RefCell::default() }

/// A diagnostic emitter that saves fatal messages to a thread local variable.
pub struct SaveEmitter;

impl Emitter for SaveEmitter {
    fn emit(&mut self, cs: Option<&MultiSpan>, message: &str, _: Option<&str>, level: Level) {
        if level == Level::Fatal {
            let span = cs.map_or(DUMMY_SP, |ms| ms.to_span_bounds());
            ERROR.with(|e| *e.borrow_mut() = Some((span, message.into())));
        }
    }

    fn custom_emit(&mut self, _: &RenderSpan, _: &str, _: Level) { }
}

// TokenReader ___________________________________

/// A token reader which wraps a `Vec<TokenAndSpan>`.
#[derive(Clone)]
struct TokenReader<'s> {
    session: &'s ParseSess,
    tokens: Vec<TokenAndSpan>,
    index: usize,
}

impl<'s> TokenReader<'s> {
    //- Constructors -----------------------------

    fn new(session: &'s ParseSess, tokens: Vec<TokenAndSpan>) -> TokenReader<'s> {
        TokenReader { session: session, tokens: tokens, index: 0 }
    }
}

impl<'s> Reader for TokenReader<'s> {
    fn is_eof(&self) -> bool {
        self.index + 1 == self.tokens.len()
    }

    fn next_token(&mut self) -> TokenAndSpan {
        let next = self.tokens[self.index].clone();
        if !self.is_eof() {
            self.index += 1;
        }
        next
    }

    fn fatal(&self, message: &str) -> FatalError {
        self.session.span_diagnostic.span_fatal(self.peek().sp, message)
    }

    fn err(&self, message: &str) {
        self.session.span_diagnostic.span_err(self.peek().sp, message);
    }

    fn peek(&self) -> TokenAndSpan {
        self.tokens[self.index].clone()
    }
}

// TransactionParser _____________________________

/// A wrapper around a `Parser` which allows for rolling back parsing actions.
pub struct TransactionParser<'s> {
    session: &'s ParseSess,
    tokens: Vec<TokenAndSpan>,
    start: usize,
    last: usize,
}

impl<'s> TransactionParser<'s> {
    //- Constructors -----------------------------

    pub fn new(session: &'s ParseSess, tts: &[TokenTree]) -> TransactionParser<'s> {
        let mut parser = TransactionParser { session: session, tokens: vec![], start: 0, last: 0 };

        let handler = &session.span_diagnostic;
        let mut reader = transcribe::new_tt_reader(handler, None, None, tts.into());
        while !reader.is_eof() {
            parser.tokens.push(reader.next_token());
        }
        parser.tokens.push(reader.next_token());

        parser
    }

    //- Accessors --------------------------------

    /// Returns the span of the last token processed.
    pub fn get_last_span(&self) -> Span {
        if self.last == self.tokens.len() {
            self.tokens[self.tokens.len() - 1].sp
        } else {
            self.tokens[self.last].sp
        }
    }

    /// Returns whether this parser has successfully processed all of its tokens.
    pub fn is_empty(&self) -> bool {
        self.last == self.tokens.len() - 1
    }

    //- Mutators ---------------------------------

    pub fn start(&mut self) {
        self.start = self.last;
    }

    pub fn rollback(&mut self) {
        self.last = self.start;
    }

    pub fn apply<T, F: FnOnce(&mut Parser<'s>) -> T>(&mut self, f: F) -> T {
        let reader = Box::new(TokenReader::new(self.session, self.tokens[self.last..].into()));
        let mut parser = Parser::new(self.session, vec![], reader);
        let result = f(&mut parser);
        self.last += parser.tokens_consumed;
        result
    }

    pub fn parse<T, F: FnOnce(&mut Parser<'s>) -> PResult<'s, T>>(
        &mut self, f: F
    ) -> PluginResult<T> {
        self.apply(f).map_err(|mut db| {
            db.cancel();
            ERROR.with(|e| e.borrow().clone().unwrap_or_else(|| (DUMMY_SP, "no error".into())))
        })
    }

    pub fn parse2<T, F: FnOnce(&mut Parser<'s>) -> PResult<'s, T>>(
        &mut self, description: &str, name: &str, f: F
    ) -> PluginResult<T> {
        self.apply(f).map_err(|mut db| {
            db.cancel();
            (self.get_last_span(), format!("expected {}: '{}'", description, name))
        })
    }

    parse!(parse_attribute(true), "attribute", Attribute);
    parse!(parse_block(), "block", P<Block>);
    parse!(parse_expr(), "expression", P<Expr>);
    parse!(parse_ident(), "identifier", Ident);
    parse!(OPTION: parse_item(), "item", P<Item>);
    parse!(parse_lifetime(), "lifetime", Lifetime);
    parse!(parse_lit(), "literal", Lit);
    parse!(parse_meta_item(), "meta item", P<MetaItem>);
    parse!(parse_pat(), "pattern", P<Pat>);
    parse!(parse_path(PathParsingMode::LifetimeAndTypesWithoutColons), "path", Path);
    parse!(OPTION: parse_stmt(), "statement", Stmt);
    parse!(parse_ty(), "type", P<Ty>);
    parse!(parse_token_tree(), "token tree", TokenTree);
}

// TtsIterator ___________________________________

/// A wraper around an iterator of `TokenTree`s.
pub struct TtsIterator<'i, I> where I: Iterator<Item=&'i TokenTree> {
    pub error: (Span, String),
    pub iterator: I,
    lifetime: PhantomData<&'i ()>,
}

impl<'i, I> TtsIterator<'i, I> where I: Iterator<Item=&'i TokenTree> {
    //- Constructors -----------------------------

    pub fn new(iterator: I, span: Span, message: &str) -> TtsIterator<'i, I> {
        TtsIterator { error: (span, message.into()), iterator: iterator, lifetime: PhantomData }
    }

    //- Mutators ---------------------------------

    pub fn expect(&mut self) -> PluginResult<&'i TokenTree> {
        self.iterator.next().ok_or_else(|| self.error.clone())
    }

    pub fn expect_token(&mut self, description: &str) -> PluginResult<(Span, Token)> {
        self.expect().and_then(|tt| {
            match *tt {
                TokenTree::Token(span, ref token) => Ok((span, token.clone())),
                _ => tt.to_error(format!("expected {}", description)),
            }
        })
    }

    pub fn expect_specific_token(&mut self, token: Token) -> PluginResult<()> {
        let description = Parser::token_to_string(&token);
        self.expect_token(&description).and_then(|(s, t)| {
            if t.mtwt_eq(&token) {
                Ok(())
            } else {
                s.to_error(format!("expected {}", description))
            }
        })
    }
}

impl<'i, I> Iterator for TtsIterator<'i, I> where I: Iterator<Item=&'i TokenTree> {
    type Item = &'i TokenTree;

    fn next(&mut self) -> Option<&'i TokenTree> {
        self.iterator.next()
    }
}

//================================================
// Functions
//================================================

pub fn mk_path(context: &ExtCtxt, idents: &[&str]) -> Vec<Ident> {
    idents.iter().map(|i| context.ident_of(i)).collect()
}

pub fn mk_expr_call(context: &ExtCtxt, span: Span, idents: &[&str], args: Vec<P<Expr>>) -> P<Expr> {
    context.expr_call_global(span, mk_path(context, idents), args)
}

pub fn mk_expr_path(context: &ExtCtxt, span: Span, idents: &[&str]) -> P<Expr> {
    context.expr_path(context.path_global(span, mk_path(context, idents)))
}
