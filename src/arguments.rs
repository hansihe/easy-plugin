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
use syntax::codemap::{DUMMY_SP, CodeMap, Span};
use syntax::errors::{Handler};
use syntax::parse::{ParseSess};
use syntax::parse::common::{SeqSep};
use syntax::parse::parser::{Parser};
use syntax::parse::token::{BinOpToken, Token};
use syntax::ptr::{P};

use super::{Amount, PluginResult, Specifier};
use super::utility::{SaveEmitter, ToError, TransactionParser};

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
    BinOp(BinOpToken),
    /// A brace-delimited sequence of statements (e.g., `{ log(error, "hi"); return 12; }`).
    Block(P<Block>),
    /// A delimited sequence of token trees (e.g., `()`, `[foo - "bar"]`).
    Delim(Rc<Delimited>),
    /// An expression (e.g., `2 + 2`, `if true { 1 } else { 2 }`, `f(42)`).
    Expr(P<Expr>),
    /// An identifier (e.g., `x`, `foo`).
    Ident(Ident),
    /// An item (e.g., `fn foo() { }`, `struct Bar;`).
    Item(P<Item>),
    /// A lifetime (e.g., `'a`).
    Lftm(Name),
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
    Tok(Token),
    /// A single token tree.
    Tt(TokenTree),
    /// A sequence which may either contain sequence matches or subsequences.
    Sequence(Vec<Match>),
    /// A count of named sequence repetitions.
    NamedSequence(usize),
}

impl Match {
    //- Accessors --------------------------------

    /// Returns this attribute match.
    ///
    /// # Panics
    ///
    /// * this match is not an attribute
    pub fn as_attr(&self) -> Attribute {
        match *self {
            Match::Attr(ref attr) => attr.clone(),
            _ => panic!("this match is not an attribute"),
        }
    }

    /// Returns this binary operator match.
    ///
    /// # Panics
    ///
    /// * this match is not a binary operator
    pub fn as_binop(&self) -> BinOpToken {
        match *self {
            Match::BinOp(binop) => binop,
            _ => panic!("this match is not a binary operator"),
        }
    }

    /// Returns this block match.
    ///
    /// # Panics
    ///
    /// * this match is not a block
    pub fn as_block(&self) -> P<Block> {
        match *self {
            Match::Block(ref block) => block.clone(),
            _ => panic!("this match is not a block"),
        }
    }

    /// Returns this delimited match.
    ///
    /// # Panics
    ///
    /// * this match is not a delimited sequence of token trees
    pub fn as_delim(&self) -> Rc<Delimited> {
        match *self {
            Match::Delim(ref delimited) => delimited.clone(),
            _ => panic!("this match is not a delimited sequence of token trees"),
        }
    }

    /// Returns this expression match.
    ///
    /// # Panics
    ///
    /// * this match is not an expression
    pub fn as_expr(&self) -> P<Expr> {
        match *self {
            Match::Expr(ref expr) => expr.clone(),
            _ => panic!("this match is not an expression"),
        }
    }

    /// Returns this identifier match.
    ///
    /// # Panics
    ///
    /// * this match is not an identifier
    pub fn as_ident(&self) -> Ident {
        match *self {
            Match::Ident(ident) => ident,
            _ => panic!("this match is not an identifier"),
        }
    }

    /// Returns this item match.
    ///
    /// # Panics
    ///
    /// * this match is not an item
    pub fn as_item(&self) -> P<Item> {
        match *self {
            Match::Item(ref item) => item.clone(),
            _ => panic!("this match is not an item"),
        }
    }

    /// Returns this lifetime match.
    ///
    /// # Panics
    ///
    /// * this match is not a lifetime
    pub fn as_lftm(&self) -> Name {
        match *self {
            Match::Lftm(lftm) => lftm,
            _ => panic!("this match is not a lifetime"),
        }
    }

    /// Returns this literal match.
    ///
    /// # Panics
    ///
    /// * this match is not a literal
    pub fn as_lit(&self) -> Lit {
        match *self {
            Match::Lit(ref lit) => lit.clone(),
            _ => panic!("this match is not a literal"),
        }
    }

    /// Returns this "meta" item match.
    ///
    /// # Panics
    ///
    /// * this match is not a "meta" item
    pub fn as_meta(&self) -> P<MetaItem> {
        match *self {
            Match::Meta(ref meta) => meta.clone(),
            _ => panic!("this match is not a \"meta\" item"),
        }
    }

    /// Returns this pattern match.
    ///
    /// # Panics
    ///
    /// * this match is not a pattern
    pub fn as_pat(&self) -> P<Pat> {
        match *self {
            Match::Pat(ref pat) => pat.clone(),
            _ => panic!("this match is not a pattern"),
        }
    }

    /// Returns this path match.
    ///
    /// # Panics
    ///
    /// * this match is not a path
    pub fn as_path(&self) -> Path {
        match *self {
            Match::Path(ref path) => path.clone(),
            _ => panic!("this match is not a path"),
        }
    }

    /// Returns this statement match.
    ///
    /// # Panics
    ///
    /// * this match is not a statement
    pub fn as_stmt(&self) -> Stmt {
        match *self {
            Match::Stmt(ref stmt) => stmt.clone(),
            _ => panic!("this match is not a statement"),
        }
    }

    /// Returns this type match.
    ///
    /// # Panics
    ///
    /// * this match is not a type
    pub fn as_ty(&self) -> P<Ty> {
        match *self {
            Match::Ty(ref ty) => ty.clone(),
            _ => panic!("this match is not a type"),
        }
    }

    /// Returns this token match.
    ///
    /// # Panics
    ///
    /// * this match is not a token
    pub fn as_tok(&self) -> Token {
        match *self {
            Match::Tok(ref tok) => tok.clone(),
            _ => panic!("this match is not a token"),
        }
    }

    /// Returns this token tree match.
    ///
    /// # Panics
    ///
    /// * this match is not a token tree
    pub fn as_tt(&self) -> TokenTree {
        match *self {
            Match::Tt(ref tt) => tt.clone(),
            _ => panic!("this match is not a token tree"),
        }
    }

    /// Returns this collection of sequence matches or subsequences.
    ///
    /// # Panics
    ///
    /// * this match is not a collection of sequence matches or subsequences
    pub fn as_sequence(&self) -> Vec<Match> {
        match *self {
            Match::Sequence(ref sequence) => sequence.clone(),
            _ => panic!("this match is not a collection of sequence matches or subsequences"),
        }
    }

    /// Returns this count of named sequence repetitions.
    ///
    /// # Panics
    ///
    /// * this match is not a count of named sequence reptitions
    pub fn as_named_sequence(&self) -> usize {
        match *self {
            Match::NamedSequence(count) => count,
            _ => panic!("this match is not a count of named sequence reptitions"),
        }
    }

    /// Returns whether this count of named sequence repetitions is non-zero.
    ///
    /// # Panics
    ///
    /// * this match is not a count of named sequence reptitions
    pub fn as_named_sequence_bool(&self) -> bool {
        match *self {
            Match::NamedSequence(count) => count != 0,
            _ => panic!("this match is not a count of named sequence reptitions"),
        }
    }
}

//================================================
// Structs
//================================================

// ArgumentParser ________________________________

/// Parses arguments.
struct ArgumentParser<'s> {
    parser: TransactionParser<'s>,
    span: Span,
}

impl<'s> ArgumentParser<'s> {
    //- Constructors -----------------------------

    fn new(session: &'s ParseSess, tts: &'s [TokenTree], span: Span) -> ArgumentParser<'s> {
        ArgumentParser { span: span, parser: TransactionParser::new(&session, tts.into()) }
    }

    //- Mutators ---------------------------------

    fn expect_token(&mut self) -> PluginResult<Token> {
        match self.parser.apply(|p| p.bump_and_get()) {
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
                if count != 0 && !self.parser.apply(|p| p.eat(separator)) {
                    return Ok(count);
                }
            }

            let mut submatches = HashMap::new();
            match self.parse_arguments(&specification, &mut submatches) {
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

        for specifier in specification {
            match *specifier {
                Specifier::Attr(ref name) => insert!(Attr, parse_attribute, name),
                Specifier::BinOp(ref name) => match try!(self.expect_token()) {
                    Token::BinOp(binop) | Token::BinOpEq(binop) => {
                        matches.insert(name.clone(), Match::BinOp(binop));
                    },
                    _ => {
                        let error = format!("expected binop: '{}'", name);
                        return self.parser.get_last_span().to_error(error);
                    },
                },
                Specifier::Block(ref name) => insert!(Block, parse_block, name),
                Specifier::Delim(ref name) => {
                    let delim = try!(self.parse_delim());
                    matches.insert(name.clone(), Match::Delim(delim));
                },
                Specifier::Expr(ref name) => insert!(Expr, parse_expr, name),
                Specifier::Ident(ref name) => insert!(Ident, parse_ident, name),
                Specifier::Item(ref name) => insert!(Item, parse_item, name),
                Specifier::Lftm(ref name) => insert!(Lftm, parse_lifetime.name, name),
                Specifier::Lit(ref name) => insert!(Lit, parse_lit, name),
                Specifier::Meta(ref name) => insert!(Meta, parse_meta_item, name),
                Specifier::Pat(ref name) => insert!(Pat, parse_pat, name),
                Specifier::Path(ref name) => insert!(Path, parse_path, name),
                Specifier::Stmt(ref name) => insert!(Stmt, parse_stmt, name),
                Specifier::Ty(ref name) => insert!(Ty, parse_ty, name),
                Specifier::Tok(ref name) => {
                    let tok = try!(self.expect_token());
                    matches.insert(name.clone(), Match::Tok(tok));
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
                    let separator = separator.as_ref();
                    let count = self.parse_sequence(amount, separator, specification, matches);
                    matches.insert(name.clone(), Match::NamedSequence(try!(count)));
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
            self.span.to_error("too many arguments")
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
            assert_eq!(m.get("binop").unwrap().as_binop(), BinOpToken::Plus);
            check!(block_to_string, &get!(m, block, as_block), "{ let a = 322; a }");

            let delim = get!(m, delim, as_delim);
            assert_eq!(delim.delim, DelimToken::Bracket);
            check!(tts_to_string, delim.tts, "1 , 2 , 3");

            check!(expr_to_string, &get!(m, expr, as_expr), "2 + 2");
            assert_eq!(&*get!(m, ident, as_ident).name.as_str(), "foo");
            check!(item_to_string, &get!(m, item, as_item), "struct Bar;");
            assert_eq!(&*get!(m, lftm, as_lftm).as_str(), "'baz");
            check!(lit_to_string, get!(m, lit, as_lit), "322");
            check!(meta_item_to_string, &get!(m, meta, as_meta), r#"cfg(target_os = "windows")"#);
            check!(pat_to_string, &get!(m, pat, as_pat), r#"(foo, "bar")"#);
            check!(path_to_string, get!(m, path, as_path), "::std::vec::Vec<i32>");
            check!(stmt_to_string, &get!(m, stmt, as_stmt), "let a = 322;");
            check!(ty_to_string, &get!(m, ty, as_ty), "i32");
            check!(token_to_string, get!(m, tok, as_tok), "~");
            check!(tt_to_string, get!(m, tt, as_tt), "!");
        });

        let arguments = "a, b c, d e f; ; g";
        let specification = "$($a:ident $($b:ident)*), +; $($c:ident)?; $($d:ident)?";

        with_matches(arguments, specification, |m| {
            assert_eq!(m.len(), 4);

            let a = get!(m, a, as_sequence, as_ident);
            assert_eq!(a.len(), 3);

            assert_eq!(a[0].name.as_str(), "a");
            assert_eq!(a[1].name.as_str(), "b");
            assert_eq!(a[2].name.as_str(), "d");

            let b = get!(m, b, as_sequence, as_sequence, as_ident);
            assert_eq!(b.len(), 3);

            assert_eq!(b[0].len(), 0);

            assert_eq!(b[1].len(), 1);
            assert_eq!(b[1][0].name.as_str(), "c");

            assert_eq!(b[2].len(), 2);
            assert_eq!(b[2][0].name.as_str(), "e");
            assert_eq!(b[2][1].name.as_str(), "f");

            let c = get!(m, c, as_sequence, as_ident);
            assert_eq!(c.len(), 0);

            let d = get!(m, d, as_sequence, as_ident);
            assert_eq!(d.len(), 1);

            assert_eq!(d[0].name.as_str(), "g");
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

            assert_eq!(b[0].name.as_str(), "a");
            assert_eq!(b[1].name.as_str(), "b");

            check!(lit_to_string, get!(m, c, as_lit), "3");
        });

        let arguments = ", A, A A B, B, B D";
        let specification = "$($a:(A)*), + $b:(B), + $c:(C)? $d:(D)?";

        with_matches(arguments, specification, |m| {
            assert_eq!(m.len(), 4);

            let a = get!(m, a, as_sequence, as_named_sequence);
            assert_eq!(a.len(), 3);

            assert_eq!(a[0], 0);
            assert_eq!(a[1], 1);
            assert_eq!(a[2], 2);

            assert_eq!(get!(m, b, as_named_sequence), 3);
            assert_eq!(get!(m, c, as_named_sequence), 0);
            assert_eq!(get!(m, d, as_named_sequence), 1);
        });

        let arguments = "a, b, c,";
        let specification = "$($a:ident), +,";

        with_matches(arguments, specification, |m| {
            assert_eq!(m.len(), 1);

            let a = get!(m, a, as_sequence, as_ident);
            assert_eq!(a.len(), 3);

            assert_eq!(a[0].name.as_str(), "a");
            assert_eq!(a[1].name.as_str(), "b");
            assert_eq!(a[2].name.as_str(), "c");
        });
    }
}
