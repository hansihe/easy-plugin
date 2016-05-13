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

use std::collections::{HashMap};
use std::rc::{Rc};

use syntax::ast::*;
use syntax::codemap::{self, DUMMY_SP, CodeMap, Span, Spanned};
use syntax::errors::{Handler};
use syntax::parse::{ParseSess};
use syntax::parse::common::{SeqSep};
use syntax::parse::parser::{Parser};
use syntax::parse::token::{BinOpToken, Token};
use syntax::ptr::{P};

use super::{Amount, PluginResult, Specifier};
use super::utility::{SaveEmitter, ToError, TransactionParser};

//================================================
// Macros
//================================================

// from! _________________________________________

macro_rules! from {
    ($name:ident, $variant:ident, $ty:ty) => {
        impl Match {
            #[allow(missing_docs)]
            pub fn $name(&self) -> $ty {
                match *self {
                    Match::$variant(ref value) => value.clone(),
                    _ => panic!("expected `Match::{}`", stringify!($variant)),
                }
            }
        }

        impl<'a> From<&'a Match> for $ty {
            fn from(match_: &'a Match) -> $ty {
                match_.$name()
            }
        }
    };
}

//================================================
// Enums
//================================================

// Match _________________________________________

/// A plugin argument that has been matched with a named specifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Match {
    /// An attribute (e.g., `#[cfg(target_os = "windows")]`).
    Attr(Attribute),
    /// A binary operator (e.g., `+`, `*`).
    BinOp(Spanned<BinOpToken>),
    /// A brace-delimited sequence of statements (e.g., `{ log(error, "hi"); return 12; }`).
    Block(P<Block>),
    /// A delimited sequence of token trees (e.g., `()`, `[foo - "bar"]`).
    Delim(Spanned<Rc<Delimited>>),
    /// An expression (e.g., `2 + 2`, `if true { 1 } else { 2 }`, `f(42)`).
    Expr(P<Expr>),
    /// An identifier (e.g., `x`, `foo`).
    Ident(Spanned<Ident>),
    /// An item (e.g., `fn foo() { }`, `struct Bar;`).
    Item(P<Item>),
    /// A lifetime (e.g., `'a`).
    Lftm(Spanned<Name>),
    /// A literal (e.g., `322`, `'a'`, `"foo"`).
    Lit(Lit),
    /// A "meta" item, as found in attributes (e.g., `cfg(target_os = "windows")`).
    Meta(P<MetaItem>),
    /// A pattern (e.g., `Some(t)`, `(17, 'a')`, `_`).
    Pat(P<Pat>),
    /// A qualified name (e.g., `T::SpecialA`).
    Path(Path),
    /// A single statement (e.g., `let x = 3`).
    Stmt(Stmt),
    /// A type (e.g., `i32`, `Vec<(char, String)>`, `&T`).
    Ty(P<Ty>),
    /// A single token.
    Tok(Spanned<Token>),
    /// A single token tree.
    Tt(TokenTree),
    /// A sequence which may either contain sequence matches or subsequences.
    Sequence(Vec<Match>),
    /// A count of named sequence repetitions.
    NamedSequence(Spanned<usize>),
}

impl Match {
    //- Accessors --------------------------------

    #[allow(missing_docs)]
    pub fn as_named_sequence(&self) -> Spanned<usize> {
        match *self {
            Match::NamedSequence(count) => count,
            _ => unreachable!(),
        }
    }

    #[allow(missing_docs)]
    pub fn as_named_sequence_bool(&self) -> Spanned<bool> {
        match *self {
            Match::NamedSequence(count) => codemap::respan(count.span, count.node != 0),
            _ => unreachable!(),
        }
    }
}

from!(as_attr, Attr, Attribute);
from!(as_bin_op, BinOp, Spanned<BinOpToken>);
from!(as_block, Block, P<Block>);
from!(as_delim, Delim, Spanned<Rc<Delimited>>);
from!(as_expr, Expr, P<Expr>);
from!(as_ident, Ident, Spanned<Ident>);
from!(as_item, Item, P<Item>);
from!(as_lftm, Lftm, Spanned<Name>);
from!(as_lit, Lit, Lit);
from!(as_meta, Meta, P<MetaItem>);
from!(as_pat, Pat, P<Pat>);
from!(as_path, Path, Path);
from!(as_stmt, Stmt, Stmt);
from!(as_ty, Ty, P<Ty>);
from!(as_tok, Tok, Spanned<Token>);
from!(as_tt, Tt, TokenTree);
from!(as_sequence, Sequence, Vec<Match>);

impl<'a> From<&'a Match> for Spanned<usize> {
    fn from(match_: &'a Match) -> Spanned<usize> {
        match_.as_named_sequence()
    }
}

impl<'a> From<&'a Match> for Spanned<bool> {
    fn from(match_: &'a Match) -> Spanned<bool> {
        match_.as_named_sequence_bool()
    }
}

//================================================
// Structs
//================================================

// ArgumentParser ________________________________

struct ArgumentParser<'s> {
    parser: TransactionParser<'s>,
    span: Span,
}

impl<'s> ArgumentParser<'s> {
    //- Constructors -----------------------------

    fn new(session: &'s ParseSess, tts: &'s [TokenTree], span: Span) -> ArgumentParser<'s> {
        ArgumentParser { parser: TransactionParser::new(session, tts.into()), span: span }
    }

    //- Mutators ---------------------------------

    fn expect_token(&mut self) -> PluginResult<Token> {
        match self.parser.bump_and_get() {
            Token::Eof => self.span.to_error("unexpected end of arguments"),
            token => Ok(token),
        }
    }

    fn expect_specific_token(&mut self, token: &Token) -> PluginResult<()> {
        let found = try!(self.expect_token());
        if found.mtwt_eq(token) {
            Ok(())
        } else {
            let message = format!("expected `{}`", Parser::token_to_string(token));
            self.parser.get_last_span().to_error(message)
        }
    }

    fn parse_sequence(
        &mut self,
        amount: Amount,
        separator: Option<&Token>,
        specification: &[Specifier],
        matches: &mut HashMap<String, Match>,
    ) -> PluginResult<usize> {
        for specifier in specification {
            if let Some(name) = specifier.get_name() {
                matches.insert(name.clone(), Match::Sequence(vec![]));
            }
        }

        let required = amount == Amount::OneOrMore;
        let mut count = 0;

        loop {
            self.parser.start();
            if let Some(ref separator) = separator {
                if count != 0 && !self.parser.eat(separator) {
                    return Ok(count);
                }
            }

            let mut submatches = HashMap::new();
            match self.parse_arguments(specification, &mut submatches) {
                Ok(()) => { },
                Err(error) => if count == 0 && required {
                    return Err(error);
                } else {
                    self.parser.rollback();
                    return Ok(count);
                },
            }
            for (k, v) in submatches {
                match *matches.entry(k).or_insert_with(|| Match::Sequence(vec![])) {
                    Match::Sequence(ref mut sequence) => sequence.push(v),
                    _ => unreachable!(),
                }
            }

            count += 1;
            if amount == Amount::ZeroOrOne {
                return Ok(count);
            }
        }
    }

   fn parse_delim(&mut self) -> PluginResult<Rc<Delimited>> {
        let (delimiter, open) = match try!(self.expect_token()) {
            Token::OpenDelim(delimiter) => (delimiter, self.parser.get_last_span()),
            invalid => {
                let string = Parser::token_to_string(&invalid);
                let error = format!("expected opening delimiter, found `{}`", string);
                return self.parser.get_last_span().to_error(error);
            },
        };
        let tts = self.parser.parse(|p| {
            let sep = SeqSep { sep: None, trailing_sep_allowed: false };
            p.parse_seq_to_end(&Token::CloseDelim(delimiter), sep, |p| p.parse_token_tree())
        });
        let delimited = Delimited {
            delim: delimiter,
            open_span: open,
            tts: try!(tts),
            close_span: self.parser.get_last_span(),
        };
        Ok(Rc::new(delimited))
    }

    #[cfg_attr(feature="clippy", allow(cyclomatic_complexity))]
    fn parse_arguments(
        &mut self, specification: &[Specifier], matches: &mut HashMap<String, Match>
    ) -> PluginResult<()> {
        macro_rules! insert {
            ($variant:ident, $parse:ident$(.$field:ident)*, $name:expr) => ({
                let match_ = try!(self.parser.$parse($name))$(.$field)*;
                matches.insert($name.clone(), Match::$variant(match_));
            });
        }

        macro_rules! insert_spanned {
            ($variant:ident, $parse:ident$(.$field:ident)*, $name:expr) => ({
                let open = self.parser.get_span();
                let match_ = try!(self.parser.$parse($name))$(.$field)*;
                let spanned = codemap::spanned(open.lo, self.parser.get_last_span().hi, match_);
                matches.insert($name.clone(), Match::$variant(spanned));
            });
        }

        for specifier in specification {
            match *specifier {
                Specifier::Attr(ref name) => insert!(Attr, parse_attribute, name),
                Specifier::BinOp(ref name) => match try!(self.expect_token()) {
                    Token::BinOp(binop) | Token::BinOpEq(binop) => {
                        let spanned = codemap::respan(self.parser.get_last_span(), binop);
                        matches.insert(name.clone(), Match::BinOp(spanned));
                    },
                    _ => {
                        let error = format!("expected binop: '{}'", name);
                        return self.parser.get_last_span().to_error(error);
                    },
                },
                Specifier::Block(ref name) => insert!(Block, parse_block, name),
                Specifier::Delim(ref name) => {
                    let open = self.parser.get_span();
                    let delim = try!(self.parse_delim());
                    let spanned = codemap::spanned(open.lo, delim.close_span.hi, delim);
                    matches.insert(name.clone(), Match::Delim(spanned));
                },
                Specifier::Expr(ref name) => insert!(Expr, parse_expr, name),
                Specifier::Ident(ref name) => insert_spanned!(Ident, parse_ident, name),
                Specifier::Item(ref name) => insert!(Item, parse_item, name),
                Specifier::Lftm(ref name) => insert_spanned!(Lftm, parse_lifetime.name, name),
                Specifier::Lit(ref name) => insert!(Lit, parse_lit, name),
                Specifier::Meta(ref name) => {
                    let meta = try!(self.parser.parse_meta_item(name)).map(|mut m| {
                        m.span.hi = self.parser.get_last_span().hi;
                        m
                    });
                    matches.insert(name.clone(), Match::Meta(meta));
                },
                Specifier::Pat(ref name) => insert!(Pat, parse_pat, name),
                Specifier::Path(ref name) => insert!(Path, parse_path, name),
                Specifier::Stmt(ref name) => insert!(Stmt, parse_stmt, name),
                Specifier::Ty(ref name) => insert!(Ty, parse_ty, name),
                Specifier::Tok(ref name) => {
                    let tok = try!(self.expect_token());
                    let spanned = codemap::respan(self.parser.get_last_span(), tok);
                    matches.insert(name.clone(), Match::Tok(spanned));
                },
                Specifier::Tt(ref name) => insert!(Tt, parse_token_tree, name),
                Specifier::Specific(ref expected) => try!(self.expect_specific_token(expected)),
                Specifier::Delimited(delimiter, ref specification) => {
                    try!(self.expect_specific_token(&Token::OpenDelim(delimiter)));
                    try!(self.parse_arguments(&specification, matches));
                    try!(self.expect_specific_token(&Token::CloseDelim(delimiter)));
                },
                Specifier::Sequence(amount, ref separator, ref specification) => {
                    try!(self.parse_sequence(amount, separator.as_ref(), specification, matches));
                },
                Specifier::NamedSequence(ref name, amount, ref separator, ref specification) => {
                    let open = self.parser.get_last_span();
                    let separator = separator.as_ref();
                    let count = self.parse_sequence(amount, separator, specification, matches);
                    let close = self.parser.get_last_span();
                    let spanned = codemap::spanned(open.lo, close.hi, try!(count));
                    matches.insert(name.clone(), Match::NamedSequence(spanned));
                },
            }
        }

        Ok(())
    }

    pub fn parse(mut self, specification: &[Specifier]) -> PluginResult<HashMap<String, Match>> {
        let mut matches = HashMap::new();
        try!(self.parse_arguments(specification, &mut matches));
        if self.parser.is_empty() {
            Ok(matches)
        } else {
            let start = self.parser.get_span();
            let span = Span { lo: start.lo, hi: self.span.hi, expn_id: self.span.expn_id };
            span.to_error("too many arguments")
        }
    }
}

//================================================
// Functions
//================================================

/// Parses the supplied arguments with the supplied specification.
pub fn parse_arguments(
    session: &ParseSess, tts: &[TokenTree], specification: &[Specifier]
) -> PluginResult<HashMap<String, Match>> {
    if tts.is_empty() && specification.is_empty() {
        return Ok(HashMap::new());
    }

    let start = tts.iter().nth(0).map_or(DUMMY_SP, |s| s.get_span());
    let end = tts.iter().last().map_or(DUMMY_SP, |s| s.get_span());
    let span = Span { lo: start.lo, hi: end.hi, expn_id: start.expn_id };

    if !tts.is_empty() && specification.is_empty() {
        return span.to_error("too many arguments");
    }

    let handler = Handler::with_emitter(false, false, Box::new(SaveEmitter));
    let mut codemap = CodeMap::new();
    codemap.files = session.codemap().files.clone();
    let session = ParseSess::with_span_handler(handler, Rc::new(codemap));
    ArgumentParser::new(&session, tts, span).parse(specification)
}

//================================================
// Tests
//================================================

#[cfg(test)]
mod tests {
    use super::*;

    use std::collections::{HashMap};

    use syntax::parse;
    use syntax::ast::*;
    use syntax::parse::{ParseSess};
    use syntax::parse::token::{BinOpToken, DelimToken};

    fn parse_token_trees(source: &str) -> (ParseSess, Vec<TokenTree>) {
        let session = ParseSess::new();
        let source = source.into();
        let tts = {
            let mut parser = parse::new_parser_from_source_str(&session, vec![], "".into(), source);
            parser.parse_all_token_trees().unwrap()
        };
        (session, tts)
    }

    fn with_matches<F>(
        arguments: &str, specification: &str, f: F
    ) where F: Fn(HashMap<String, Match>) {
        let (session, arguments) = parse_token_trees(arguments);
        let specification = super::super::parse_specification(&parse_token_trees(specification).1);
        f(parse_arguments(&session, &arguments, specification.as_ref().unwrap()).unwrap());
    }

    #[test]
    fn test_parse_arguments() {
        macro_rules! check {
            ($print:ident, $actual:expr, $expected:expr) => ({
                assert_eq!(::syntax::print::pprust::$print(&$actual), $expected);
            });
        }

        macro_rules! get {
            ($matches:expr, $name:ident, $as_:ident) => ({
                $matches.get(stringify!($name)).unwrap().$as_()
            });

            ($matches:expr, $name:ident, as_sequence, $as_:ident) => ({
                get!($matches, $name, as_sequence).into_iter().map(|m| m.$as_()).collect::<Vec<_>>()
            });

            ($matches:expr, $name:ident, as_sequence, as_sequence, $as_:ident) => ({
                get!($matches, $name, as_sequence).into_iter().map(|m| {
                    m.as_sequence().into_iter().map(|m| m.$as_()).collect::<Vec<_>>()
                }).collect::<Vec<_>>()
            });
        }

        with_matches("", "", |m| assert_eq!(m.len(), 0));

        let arguments = r#"
            #[cfg(target_os = "windows")]
            +
            { let a = 322; a }
            [1, 2, 3]
            2 + 2
            foo
            struct Bar;
            'baz
            322
            cfg(target_os="windows")
            (foo, "bar")
            ::std::vec::Vec<i32>
            let a = 322
            i32
            ~
            !
        "#;

        let specification = "
            $attr:attr
            $binop:binop
            $block:block
            $delim:delim
            $expr:expr
            $ident:ident
            $item:item
            $lftm:lftm
            $lit:lit
            $meta:meta
            $pat:pat
            $path:path
            $stmt:stmt
            $ty:ty
            $tok:tok
            $tt:tt
        ";

        with_matches(arguments, specification, |m| {
            assert_eq!(m.len(), 16);

            check!(attribute_to_string, get!(m, attr, as_attr), "#[cfg(target_os = \"windows\")]");
            assert_eq!(m.get("binop").unwrap().as_bin_op().node, BinOpToken::Plus);
            check!(block_to_string, &get!(m, block, as_block), "{ let a = 322; a }");

            let delim = get!(m, delim, as_delim);
            assert_eq!(delim.node.delim, DelimToken::Bracket);
            check!(tts_to_string, delim.node.tts, "1 , 2 , 3");

            check!(expr_to_string, &get!(m, expr, as_expr), "2 + 2");
            assert_eq!(&*get!(m, ident, as_ident).node.name.as_str(), "foo");
            check!(item_to_string, &get!(m, item, as_item), "struct Bar;");
            assert_eq!(&*get!(m, lftm, as_lftm).node.as_str(), "'baz");
            check!(lit_to_string, get!(m, lit, as_lit), "322");
            check!(meta_item_to_string, &get!(m, meta, as_meta), r#"cfg(target_os = "windows")"#);
            check!(pat_to_string, &get!(m, pat, as_pat), r#"(foo, "bar")"#);
            check!(path_to_string, get!(m, path, as_path), "::std::vec::Vec<i32>");
            check!(stmt_to_string, &get!(m, stmt, as_stmt), "let a = 322;");
            check!(ty_to_string, &get!(m, ty, as_ty), "i32");
            check!(token_to_string, get!(m, tok, as_tok).node, "~");
            check!(tt_to_string, get!(m, tt, as_tt), "!");
        });

        let arguments = "a, b c, d e f; ; g";
        let specification = "$($a:ident $($b:ident)*), +; $($c:ident)?; $($d:ident)?";

        with_matches(arguments, specification, |m| {
            assert_eq!(m.len(), 4);

            let a = get!(m, a, as_sequence, as_ident);
            assert_eq!(a.len(), 3);

            assert_eq!(a[0].node.name.as_str(), "a");
            assert_eq!(a[1].node.name.as_str(), "b");
            assert_eq!(a[2].node.name.as_str(), "d");

            let b = get!(m, b, as_sequence, as_sequence, as_ident);
            assert_eq!(b.len(), 3);

            assert_eq!(b[0].len(), 0);

            assert_eq!(b[1].len(), 1);
            assert_eq!(b[1][0].node.name.as_str(), "c");

            assert_eq!(b[2].len(), 2);
            assert_eq!(b[2][0].node.name.as_str(), "e");
            assert_eq!(b[2][1].node.name.as_str(), "f");

            let c = get!(m, c, as_sequence, as_ident);
            assert_eq!(c.len(), 0);

            let d = get!(m, d, as_sequence, as_ident);
            assert_eq!(d.len(), 1);

            assert_eq!(d[0].node.name.as_str(), "g");
        });

        let arguments = "1 a 2 b 3";
        let specification = "$($a:lit $b:ident)* $c:lit";

        with_matches(arguments, specification, |m| {
            assert_eq!(m.len(), 3);

            let a = get!(m, a, as_sequence, as_lit);
            assert_eq!(a.len(), 2);

            check!(lit_to_string, a[0], "1");
            check!(lit_to_string, a[1], "2");

            let b = get!(m, b, as_sequence, as_ident);
            assert_eq!(b.len(), 2);

            assert_eq!(b[0].node.name.as_str(), "a");
            assert_eq!(b[1].node.name.as_str(), "b");

            check!(lit_to_string, get!(m, c, as_lit), "3");
        });

        let arguments = ", A, A A B, B, B D";
        let specification = "$($a:(A)*), + $b:(B), + $c:(C)? $d:(D)?";

        with_matches(arguments, specification, |m| {
            assert_eq!(m.len(), 4);

            let a = get!(m, a, as_sequence, as_named_sequence);
            assert_eq!(a.len(), 3);

            assert_eq!(a[0].node, 0);
            assert_eq!(a[1].node, 1);
            assert_eq!(a[2].node, 2);

            assert_eq!(get!(m, b, as_named_sequence).node, 3);
            assert_eq!(get!(m, c, as_named_sequence_bool).node, false);
            assert_eq!(get!(m, d, as_named_sequence_bool).node, true);
        });

        let arguments = "a, b, c,";
        let specification = "$($a:ident), +,";

        with_matches(arguments, specification, |m| {
            assert_eq!(m.len(), 1);

            let a = get!(m, a, as_sequence, as_ident);
            assert_eq!(a.len(), 3);

            assert_eq!(a[0].node.name.as_str(), "a");
            assert_eq!(a[1].node.name.as_str(), "b");
            assert_eq!(a[2].node.name.as_str(), "c");
        });
    }
}
