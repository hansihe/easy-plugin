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

//! Various utilities.

use std::cell::{RefCell};
use std::rc::{Rc};

use rustc_errors::{DiagnosticBuilder, FatalError, Handler, Level};
use rustc_errors::emitter::{Emitter};

use syntax::ext::tt::transcribe;
use syntax::ast::*;
use syntax::codemap::{CodeMap, Span, DUMMY_SP};
use syntax::parse::{ParseSess, PResult};
use syntax::parse::common::{SeqSep};
use syntax::parse::lexer::{Reader, TokenAndSpan};
use syntax::parse::parser::{Parser, PathStyle};
use syntax::parse::token::{BinOpToken, Token};
use syntax::ptr::{P};
use syntax::tokenstream::{Delimited, TokenTree};

/// A result type for reporting errors in plugins.
pub type PluginResult<T> = Result<T, (Span, String)>;

//================================================
// Macros
//================================================

// parse! _______________________________________

/// Defines a parsing method for `TransactionParser` that parses a particular AST entity.
macro_rules! parse {
    ($name:ident($($argument:expr), *)$(.$method:ident())*, $description:expr, $ty:ty) => {
        pub fn $name(&mut self, name: &str) -> PluginResult<(Span, $ty)> {
            self.parse_expected($description, name, |p| p.$name($($argument), *))
        }
    };

    (OPTION: $name:ident($($argument:expr), *)$(.$method:ident())*, $description:expr, $ty:ty) => {
        pub fn $name(&mut self, name: &str) -> PluginResult<(Span, $ty)> {
            self.parse_expected_option($description, name, |p| p.$name($($argument), *))
        }
    };
}

//================================================
// Structs
//================================================

// SaveEmitter ___________________________________

/// The most recent fatal parsing error, if any.
thread_local! { static ERROR: RefCell<Option<(Span, String)>> = RefCell::default() }

/// A diagnostic emitter that saves fatal parsing errors to a thread local variable.
struct SaveEmitter;

impl SaveEmitter {
    //- Static -----------------------------------

    /// Returns the last fatal parsing error.
    fn get_error() -> (Span, String) {
        ERROR.with(|e| e.borrow().clone().unwrap_or_else(|| (DUMMY_SP, "no error".into())))
    }
}

impl Emitter for SaveEmitter {
    fn emit(&mut self, builder: &DiagnosticBuilder) {
        if builder.level == Level::Fatal {
            let span = builder.span.primary_span().unwrap_or(DUMMY_SP);
            ERROR.with(|e| *e.borrow_mut() = Some((span, builder.message.clone())));
        }
    }
}

// TokenReader ___________________________________

/// A `Reader` that wraps a slice of `TokenAndSpan`s.
#[derive(Clone)]
struct TokenReader<'s> {
    session: &'s ParseSess,
    tokens: &'s [TokenAndSpan],
    index: usize,
}

impl<'s> TokenReader<'s> {
    //- Constructors -----------------------------

    /// Constructs a new `TokenReader`.
    fn new(session: &'s ParseSess, tokens: &'s [TokenAndSpan]) -> TokenReader<'s> {
        TokenReader { session: session, tokens: tokens, index: 0 }
    }
}

impl<'s> Reader for TokenReader<'s> {
    fn is_eof(&self) -> bool {
        self.index + 1 >= self.tokens.len()
    }

    fn try_next_token(&mut self) -> Result<TokenAndSpan, ()> {
        let next = self.tokens[self.index].clone();
        if !self.is_eof() {
            self.index += 1;
        }
        Ok(next)
    }

    fn fatal(&self, _: &str) -> FatalError { unreachable!() }
    fn err(&self, _: &str) { }
    fn emit_fatal_errors(&mut self) { }

    fn peek(&self) -> TokenAndSpan {
        self.tokens[self.index].clone()
    }
}

// Transaction ___________________________________

/// A parser transaction.
pub struct Transaction(usize);

impl Transaction {
    //- Accessors ---------------------------------

    /// Resets the parser to the state it was in when this transaction was created.
    pub fn rollback(&self, parser: &mut TransactionParser) {
        parser.index = self.0;
    }
}

// TransactionParser _____________________________

/// A wrapper around a `Parser` which allows for rolling back parsing actions.
#[allow(missing_debug_implementations)]
pub struct TransactionParser {
    session: ParseSess,
    tokens: Vec<TokenAndSpan>,
    index: usize,
    span: Span,
}

impl TransactionParser {
    //- Constructors -----------------------------

    /// Constructs a new `TransactionParser`.
    pub fn new(session: &ParseSess, tts: &[TokenTree]) -> TransactionParser {
        let handler = Handler::with_emitter(false, false, Box::new(SaveEmitter));
        let mut codemap = CodeMap::new();
        codemap.files = session.codemap().files.clone();
        TransactionParser {
            session: ParseSess::with_span_handler(handler, Rc::new(codemap)),
            tokens: flatten_tts(session, tts),
            index: 0,
            span: span_tts(tts),
        }
    }

    //- Accessors --------------------------------

    /// Returns the span of current token.
    pub fn get_span(&self) -> Span {
        self.tokens.get(self.index).map_or(self.span, |t| t.sp)
    }

    /// Returns the span of the last token processed.
    pub fn get_last_span(&self) -> Span {
        self.tokens.get(self.index.saturating_sub(1)).map_or(self.span, |t| t.sp)
    }

    /// Returns whether the current token is the EOF token.
    fn is_eof(&self) -> bool {
        self.index + 1 >= self.tokens.len()
    }

    /// Returns the span of the remaining tokens, if any.
    pub fn get_remainder_span(&self) -> Option<Span> {
        if self.is_eof() {
            None
        } else {
            Some(span_spans(self.get_span(), self.span))
        }
    }

    /// Creates a new transaction which saves the current state of this parser.
    pub fn transaction(&self) -> Transaction {
        Transaction(self.index)
    }

    /// Returns a parsing error.
    fn get_error(&self, mut span: Span, description: &str, name: Option<&str>) -> (Span, String) {
        let mut message = if let Some(name) = name {
            format!("expected {}: '{}'", description, name)
        } else {
            format!("expected {}", description)
        };
        if self.is_eof() {
            span = self.span;
            message = format!("unexpected end of arguments: {}", message);
        }
        (span, message)
    }

    //- Mutators ---------------------------------

    /// Applies a parsing action to this parser, returning the result of the action.
    #[cfg_attr(feature="clippy", allow(needless_lifetimes))]
    pub fn apply<'s, T, F: FnOnce(&mut Parser<'s>) -> T>(&'s mut self, f: F) -> (Span, T) {
        let reader = TokenReader::new(&self.session, &self.tokens[self.index..]);
        let mut parser = Parser::new(&self.session, vec![], Box::new(reader));
        let start = self.get_span();
        let result = f(&mut parser);
        self.index += parser.tokens_consumed;
        let end = self.get_last_span();
        (span_spans(start, end), result)
    }

    /// Attempts to consume the supplied token, returning whether a token was consumed.
    pub fn eat(&mut self, token: &Token) -> bool {
        self.apply(|p| p.eat(token)).1
    }

    /// Returns the next token.
    pub fn next_token(
        &mut self, description: &str, name: Option<&str>
    ) -> PluginResult<(Span, Token)> {
        match self.tokens[self.index].tok.clone() {
            Token::Eof => Err(self.get_error(DUMMY_SP, description, name)),
            token => { self.index += 1; Ok((self.get_last_span(), token)) },
        }
    }

    /// Applies a parsing action to this parser, returning the result of the action.
    fn parse_expected<'s, T, F: FnOnce(&mut Parser<'s>) -> PResult<'s, T>>(
        &'s mut self, description: &str, name: &str, f: F
    ) -> PluginResult<(Span, T)> {
        let this: *const TransactionParser = self as *const TransactionParser;
        let span = match self.apply(f) {
            (span, Ok(value)) => return Ok((span, value)),
            (span, Err(mut err)) => { err.cancel(); span },
        };
        // FIXME: hack to get around mutable borrow bug
        let error = unsafe { (*this).get_error(span, description, Some(name)) };
        Err(error)
    }

    /// Applies a parsing action to this parser, returning the result of the action.
    fn parse_expected_option<'s, T, F: FnOnce(&mut Parser<'s>) -> PResult<'s, Option<T>>>(
        &'s mut self, description: &str, name: &str, f: F
    ) -> PluginResult<(Span, T)> {
        let this: *const TransactionParser = self as *const TransactionParser;
        let span = match self.apply(f) {
            (span, Ok(Some(value))) => return Ok((span, value)),
            (span, Ok(_)) => { span },
            (span, Err(mut err)) => { err.cancel(); span },
        };
        // FIXME: hack to get around mutable borrow bug
        let error = unsafe { (*this).get_error(span, description, Some(name)) };
        Err(error)
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
    parse!(parse_path(PathStyle::Type), "path", Path);
    parse!(OPTION: parse_stmt(), "statement", Stmt);
    parse!(parse_ty(), "type", P<Ty>);
    parse!(parse_token_tree(), "token tree", TokenTree);

    pub fn parse_binop(&mut self, name: &str) -> PluginResult<(Span, BinOpToken)> {
        match try!(self.next_token("binary operator", Some(name))) {
            (span, Token::BinOp(binop)) | (span, Token::BinOpEq(binop)) => Ok((span, binop)),
            (span, _) => Err((span, "expected binary operator".into())),
        }
    }

    pub fn parse_delim(&mut self, name: &str) -> PluginResult<(Span, Delimited)> {
        let (start, delim) = match try!(self.next_token("opening delimiter", Some(name))) {
            (span, Token::OpenDelim(delim)) => (span, delim),
            (span, _) => return Err((span, "expected opening delimiter".into())),
        };
        let tts = self.apply(|p| {
            let sep = SeqSep { sep: None, trailing_sep_allowed: false };
            p.parse_seq_to_end(&Token::CloseDelim(delim), sep, |p| p.parse_token_tree())
        }).1.map_err(|mut err| { err.cancel(); SaveEmitter::get_error() });
        let end = self.get_last_span();
        let delimited = Delimited {
            delim: delim,
            open_span: start,
            tts: try!(tts),
            close_span: end,
        };
        Ok((span_spans(start, end), delimited))
    }

    pub fn parse_token(&mut self, name: &str) -> PluginResult<(Span, Token)> {
        self.next_token("token", Some(name))
    }
}

//================================================
// Functions
//================================================

/// Flattens the supplied token trees.
fn flatten_tts(session: &ParseSess, tts: &[TokenTree]) -> Vec<TokenAndSpan> {
    let mut reader = transcribe::new_tt_reader(&session.span_diagnostic, None, None, tts.into());
    let mut tokens = vec![];
    while reader.peek().tok != Token::Eof {
        tokens.push(reader.next_token());
    }
    tokens.push(reader.next_token());
    tokens
}

/// Returns a span that spans the supplied spans.
pub fn span_spans(start: Span, end: Span) -> Span {
    Span { lo: start.lo, hi: end.hi, expn_id: start.expn_id }
}

/// Returns a span that spans all of the supplied token trees.
pub fn span_tts(tts: &[TokenTree]) -> Span {
    let start = tts.get(0).map_or(DUMMY_SP, TokenTree::get_span);
    let end = tts.iter().last().map_or(DUMMY_SP, TokenTree::get_span);
    span_spans(start, end)
}
