use std::marker::{PhantomData};

use syntax::ext::tt::transcribe;
use syntax::ast::{Expr, Ident, Name, TokenTree};
use syntax::codemap::{Span};
use syntax::diagnostic::{FatalError};
use syntax::ext::base::{ExtCtxt};
use syntax::ext::build::{AstBuilder};
use syntax::parse::{ParseSess};
use syntax::parse::lexer::{Reader, TokenAndSpan};
use syntax::parse::parser::{Parser};
use syntax::parse::token::{BinOpToken, DelimToken, IdentStyle, Lit, Token};
use syntax::ptr::{P};

use super::{PluginResult};

pub trait AsExpr {
    fn as_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr>;
}

impl AsExpr for BinOpToken {
    fn as_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        let path = vec![
            context.ident_of("syntax"),
            context.ident_of("parse"),
            context.ident_of("token"),
            context.ident_of("BinOpToken"),
            context.ident_of(&format!("{:?}", self)),
        ];

        context.expr_path(context.path_global(span, path))
    }
}

impl AsExpr for DelimToken {
    fn as_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        let path = vec![
            context.ident_of("syntax"),
            context.ident_of("parse"),
            context.ident_of("token"),
            context.ident_of("DelimToken"),
            context.ident_of(&format!("{:?}", self)),
        ];

        context.expr_path(context.path_global(span, path))
    }
}

impl AsExpr for Ident {
    fn as_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        let path = vec![
            context.ident_of("syntax"),
            context.ident_of("parse"),
            context.ident_of("token"),
            context.ident_of("str_to_ident"),
        ];

        context.expr_call_global(span, path, vec![context.expr_str(span, self.name.as_str())])
    }
}

impl AsExpr for IdentStyle {
    fn as_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        let path = vec![
            context.ident_of("syntax"),
            context.ident_of("parse"),
            context.ident_of("token"),
            context.ident_of("IdentStyle"),
            context.ident_of(&format!("{:?}", self)),
        ];

        context.expr_path(context.path_global(span, path))
    }
}

impl AsExpr for Lit {
    fn as_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        macro_rules! expr {
            ($variant:expr, $($argument:expr), *) => ({
                let path = vec![
                    context.ident_of("syntax"),
                    context.ident_of("parse"),
                    context.ident_of("token"),
                    context.ident_of("Lit"),
                    context.ident_of($variant),
                ];

                let arguments = vec![$($argument), *];
                context.expr_call_global(span, path, arguments)
            });
        }

        match *self {
            Lit::Byte(name) => expr!("Byte", name.as_expr(context, span)),
            Lit::Char(name) => expr!("Char", name.as_expr(context, span)),
            Lit::Integer(name) => expr!("Integer", name.as_expr(context, span)),
            Lit::Float(name) => expr!("Float", name.as_expr(context, span)),
            Lit::Str_(name) => expr!("Str_", name.as_expr(context, span)),
            Lit::StrRaw(name, size) => {
                expr!("StrRaw", name.as_expr(context, span), context.expr_usize(span, size))
            },
            Lit::ByteStr(name) => expr!("ByteStr", name.as_expr(context, span)),
            Lit::ByteStrRaw(name, size) => {
                expr!("ByteStrRaw", name.as_expr(context, span), context.expr_usize(span, size))
            },
        }
    }
}

impl AsExpr for Name {
    fn as_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        let path = vec![
            context.ident_of("syntax"),
            context.ident_of("parse"),
            context.ident_of("token"),
            context.ident_of("intern"),
        ];

        context.expr_call_global(span, path, vec![context.expr_str(span, self.as_str())])
    }
}

impl AsExpr for Token {
    fn as_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        macro_rules! expr {
            ($variant:expr) => ({
                let path = vec![
                    context.ident_of("syntax"),
                    context.ident_of("parse"),
                    context.ident_of("token"),
                    context.ident_of("Token"),
                    context.ident_of($variant),
                ];

                context.expr_path(context.path_global(span, path))
            });

            ($variant:expr, $($argument:expr), *) => ({
                let path = vec![
                    context.ident_of("syntax"),
                    context.ident_of("parse"),
                    context.ident_of("token"),
                    context.ident_of("Token"),
                    context.ident_of($variant),
                ];

                let arguments = vec![$($argument), *];
                context.expr_call_global(span, path, arguments)
            });
        }

        match *self {
            Token::BinOp(binop) => expr!("BinOp", binop.as_expr(context, span)),
            Token::BinOpEq(binop) => expr!("BinOpEq", binop.as_expr(context, span)),
            Token::Literal(lit, suffix) => {
                expr!("Literal", lit.as_expr(context, span), suffix.as_expr(context, span))
            },
            Token::Ident(ref ident, style) => {
                expr!("Ident", ident.as_expr(context, span), style.as_expr(context, span))
            },
            Token::Lifetime(ref lifetime) => expr!("Lifetime", lifetime.as_expr(context, span)),
            Token::DocComment(comment) => expr!("DocComment", comment.as_expr(context, span)),
            Token::OpenDelim(_) |
            Token::CloseDelim(_) |
            Token::Shebang(_) |
            Token::Interpolated(_) |
            Token::MatchNt(_, _, _, _) |
            Token::SubstNt(_, _) |
            Token::SpecialVarNt(_) => unreachable!(),
            _ => expr!(&format!("{:?}", self)),
        }
    }
}

impl<T> AsExpr for Option<T> where T: AsExpr {
    fn as_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        match *self {
            Some(ref some) => {
                let some = some.as_expr(context, span);
                context.expr_some(span, some)
            },
            None => context.expr_none(span),
        }
    }
}

#[cfg_attr(feature="clippy", allow(ptr_arg))]
impl<T> AsExpr for Vec<T> where T: AsExpr {
    fn as_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        let exprs = self.iter().map(|i| i.as_expr(context, span)).collect();
        let slice = context.expr_vec_slice(span, exprs);
        context.expr_method_call(span, slice, context.ident_of("to_vec"), vec![])
    }
}

impl<T> AsExpr for [T] where T: AsExpr {
    fn as_expr(&self, context: &mut ExtCtxt, span: Span) -> P<Expr> {
        let exprs = self.iter().map(|i| i.as_expr(context, span)).collect();
        context.expr_vec_slice(span, exprs)
    }
}

pub trait AsError<T, S> where S: AsRef<str> {
    fn as_error(&self, message: S) -> PluginResult<T>;
}

impl<T, S> AsError<T, S> for Span where S: AsRef<str> {
    fn as_error(&self, message: S) -> PluginResult<T> {
        Err((self.clone(), message.as_ref().into()))
    }
}

impl<T, S> AsError<T, S> for TokenTree where S: AsRef<str> {
    fn as_error(&self, message: S) -> PluginResult<T> {
        Err((self.get_span().clone(), message.as_ref().into()))
    }
}

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
                _ => tt.as_error(format!("expected {}", description)),
            }
        })
    }

    pub fn expect_specific_token(&mut self, token: &Token) -> PluginResult<()> {
        let description = Parser::token_to_string(token);

        self.expect_token(&description).and_then(|(s, t)| {
            if t.mtwt_eq(token) {
                Ok(())
            } else {
                s.as_error(format!("expected {}", description))
            }
        })
    }

    pub fn expect_ident(&mut self) -> PluginResult<(Span, Ident)> {
        self.expect_token("identifier").and_then(|(s, t)| {
            match *t {
                Token::Ident(ref ident, _) => Ok((s, ident.clone())),
                _ => s.as_error("expected identifier"),
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

#[derive(Clone)]
pub struct TokenReader<'a> {
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

    fn fatal(&self, m: &str) -> FatalError {
        self.session.span_diagnostic.span_fatal(self.peek().sp, m)
    }

    fn err(&self, m: &str) {
        self.session.span_diagnostic.span_err(self.peek().sp, m);
    }

    fn peek(&self) -> TokenAndSpan {
        self.tokens[self.index].clone()
    }
}

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
        self.tokens[self.current].sp
    }
}
