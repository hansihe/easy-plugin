use std::marker::{PhantomData};

use syntax::ext::tt::transcribe;
use syntax::ast::{Expr, Ident, Name, TokenTree};
use syntax::codemap::{Span};
use syntax::errors::{FatalError};
use syntax::ext::base::{ExtCtxt};
use syntax::ext::build::{AstBuilder};
use syntax::parse::{ParseSess};
use syntax::parse::lexer::{Reader, TokenAndSpan};
use syntax::parse::parser::{Parser};
use syntax::parse::token::{BinOpToken, DelimToken, IdentStyle, Lit, Token};
use syntax::ptr::{P};

use super::{PluginResult};

//================================================
// Traits
//================================================

// ToError _______________________________________

/// A type that can be extended into a `PluginResult<T>`.
pub trait ToError<T, S> where S: AsRef<str> {
    /// Returns an `Err` value with the span of this value and the supplied message.
    fn to_error(&self, message: S) -> PluginResult<T>;
}

impl<T, S> ToError<T, S> for Span where S: AsRef<str> {
    fn to_error(&self, message: S) -> PluginResult<T> {
        Err((*self, message.as_ref().into()))
    }
}

impl<T, S> ToError<T, S> for TokenTree where S: AsRef<str> {
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
        mk_expr_path(context, span, &["BinOpToken", &format!("{:?}", self)])
    }
}

impl ToExpr for DelimToken {
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        mk_expr_path(context, span, &["DelimToken", &format!("{:?}", self)])
    }
}

impl ToExpr for Ident {
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        let path = mk_path(context, &["str_to_ident"]);
        context.expr_call_global(span, path, vec![context.expr_str(span, self.name.as_str())])
    }
}

impl ToExpr for IdentStyle {
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        mk_expr_path(context, span, &["IdentStyle", &format!("{:?}", self)])
    }
}

impl ToExpr for Lit {
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        macro_rules! expr {
            ($variant:expr, $name:expr) => ({
                let arguments = vec![$name.to_expr(context, span)];
                context.expr_call_global(span, mk_path(context, &["Lit", $variant]), arguments)
            });

            ($variant:expr, $name:expr, $size:expr) => ({
                let arguments = vec![$name.to_expr(context, span), context.expr_usize(span, $size)];
                context.expr_call_global(span, mk_path(context, &["Lit", $variant]), arguments)
            });
        }

        match *self {
            Lit::Byte(name) => expr!("Byte", name),
            Lit::Char(name) => expr!("Char", name),
            Lit::Integer(name) => expr!("Integer", name),
            Lit::Float(name) => expr!("Float", name),
            Lit::Str_(name) => expr!("Str_", name),
            Lit::StrRaw(name, size) => expr!("StrRaw", name, size),
            Lit::ByteStr(name) => expr!("ByteStr", name),
            Lit::ByteStrRaw(name, size) => expr!("ByteStrRaw", name, size),
        }
    }
}

impl ToExpr for Name {
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        let path = mk_path(context, &["intern"]);
        context.expr_call_global(span, path, vec![context.expr_str(span, self.as_str())])
    }
}

impl ToExpr for Token {
    fn to_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        macro_rules! expr {
            ($variant:expr, $($argument:expr), *) => ({
                let arguments = vec![$($argument.to_expr(context, span)), *];
                context.expr_call_global(span, mk_path(context, &["Token", $variant]), arguments)
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
            _ => mk_expr_path(context, span, &["Token", &format!("{:?}", self)]),
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

#[cfg_attr(feature="clippy", allow(ptr_arg))]
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

// TokenReader ___________________________________

/// A token reader which wraps a `Vec<TokenAndSpan>`.
#[derive(Clone)]
struct TokenReader<'a> {
    session: &'a ParseSess,
    tokens: Vec<TokenAndSpan>,
    index: usize,
}

impl<'a> TokenReader<'a> {
    fn new(session: &'a ParseSess, tokens: Vec<TokenAndSpan>) -> TokenReader<'a> {
        TokenReader { session: session, tokens: tokens, index: 0 }
    }
}

impl<'a> Reader for TokenReader<'a> {
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
pub struct TransactionParser<'a> {
    session: &'a ParseSess,
    tokens: Vec<TokenAndSpan>,
    current: usize,
    start: usize,
}

impl<'a> TransactionParser<'a> {
    pub fn new(session: &'a ParseSess, tts: &[TokenTree]) -> TransactionParser<'a> {
        let handler = &session.span_diagnostic;
        let mut reader = transcribe::new_tt_reader(handler, None, None, tts.into());

        let mut parser = TransactionParser {
            session: session, tokens: vec![], current: 0, start: 0
        };

        loop {
            parser.tokens.push(reader.next_token());

            if reader.is_eof() {
                parser.tokens.push(reader.next_token());
                break;
            }
        }

        parser
    }

    pub fn start(&mut self) {
        self.start = self.current;
    }

    pub fn rollback(&mut self) {
        self.current = self.start;
    }

    pub fn apply<T, F: FnOnce(&mut Parser<'a>) -> T>(&mut self, f: F) -> T {
        let reader = Box::new(TokenReader::new(self.session, self.tokens[self.current..].into()));
        let mut parser = Parser::new(self.session, vec![], reader);
        let result = f(&mut parser);
        self.current += parser.tokens_consumed;
        result
    }

    pub fn get_last_span(&self) -> Span {
        if self.current == self.tokens.len() {
            self.tokens[self.tokens.len() - 1].sp
        } else {
            self.tokens[self.current].sp
        }
    }
}

// TtsIterator ___________________________________

/// A wraper around an iterator of `TokenTree`s.
pub struct TtsIterator<'i, I> where I: Iterator<Item=&'i TokenTree> {
    pub error: (Span, String),
    pub iterator: I,
    lifetime: PhantomData<&'i ()>,
}

impl<'i, I> TtsIterator<'i, I> where I: Iterator<Item=&'i TokenTree> {
    pub fn new(iterator: I, span: Span, message: &str) -> TtsIterator<'i, I> {
        TtsIterator { error: (span, message.into()), iterator: iterator, lifetime: PhantomData }
    }

    pub fn expect(&mut self) -> PluginResult<&'i TokenTree> {
        self.iterator.next().ok_or_else(|| self.error.clone())
    }

    pub fn expect_token(&mut self, description: &str) -> PluginResult<(Span, &'i Token)> {
        self.expect().and_then(|tt| {
            match *tt {
                TokenTree::Token(span, ref token) => Ok((span, token)),
                _ => tt.to_error(format!("expected {}", description)),
            }
        })
    }

    pub fn expect_specific_token(&mut self, token: &Token) -> PluginResult<()> {
        let description = Parser::token_to_string(token);

        self.expect_token(&description).and_then(|(s, t)| {
            if t.mtwt_eq(token) {
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

fn mk_expr_path(context: &ExtCtxt, span: Span, identifiers: &[&str]) -> P<Expr> {
    context.expr_path(context.path_global(span, mk_path(context, identifiers)))
}

fn mk_path(context: &ExtCtxt, identifiers: &[&str]) -> Vec<Ident> {
    let prefix = &["syntax", "parse", "token"];
    prefix.iter().chain(identifiers.iter()).map(|i| context.ident_of(i)).collect()
}
