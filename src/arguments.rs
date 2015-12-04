use std::cell::{RefCell};
use std::collections::{HashMap};
use std::rc::{Rc};

use syntax::parse;
use syntax::ast::*;
use syntax::codemap::{DUMMY_SP, CodeMap, Span};
use syntax::diagnostic::{Emitter, Handler, Level, RenderSpan, SpanHandler};
use syntax::parse::{ParseSess};
use syntax::parse::common::{SeqSep};
use syntax::parse::parser::{Parser, PathParsingMode};
use syntax::parse::token::{BinOpToken, Token};
use syntax::ptr::{P};

use super::{Amount, PluginResult, Specifier};
use super::utility::{AsError, TransactionParser};

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
    Stmt(P<Stmt>),
    /// A type (e.g., `i32`, `Vec<(char, String)>`, `&T`).
    Ty(P<Ty>),
    /// A single token.
    Tok(Token),
    /// A single token tree.
    Tt(TokenTree),
    /// A sequence which may either contain sequence matches or subsequences.
    Sequence(Vec<Match>),
}

impl Match {
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
            Match::Ident(ident) => ident.clone(),
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
    pub fn as_stmt(&self) -> P<Stmt> {
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
}

thread_local!(static ERROR: RefCell<(Span, String)> = RefCell::new((DUMMY_SP, "no error".into())));

struct SaveEmitter;

impl SaveEmitter {
    fn emit_(&self, span: Span, message: &str) {
        ERROR.with(|e| *e.borrow_mut() = (span, message.into()));
    }
}

impl Emitter for SaveEmitter {
    fn emit(&mut self, cs: Option<(&CodeMap, Span)>, message: &str, _: Option<&str>, level: Level) {
        if level == Level::Fatal {
            self.emit_(cs.map_or(DUMMY_SP, |cs| cs.1), message);
        }
    }

    fn custom_emit(&mut self, _: &CodeMap, _: RenderSpan, _: &str, _: Level) { }
}

fn parse_sequence<'a>(
    span: Span,
    parser: &mut TransactionParser<'a>,
    amount: Amount,
    separator: &Option<Token>,
    specification: &[Specifier],
    matches: &mut HashMap<String, Match>,
) -> PluginResult<()> {
    let required = amount == Amount::OneOrMore;

    for specifier in specification {
        match *specifier {
            Specifier::Attr(ref name) |
            Specifier::BinOp(ref name) |
            Specifier::Block(ref name) |
            Specifier::Delim(ref name) |
            Specifier::Expr(ref name) |
            Specifier::Ident(ref name) |
            Specifier::Item(ref name) |
            Specifier::Lftm(ref name) |
            Specifier::Lit(ref name) |
            Specifier::Meta(ref name) |
            Specifier::Pat(ref name) |
            Specifier::Path(ref name) |
            Specifier::Stmt(ref name) |
            Specifier::Ty(ref name) |
            Specifier::Tok(ref name) |
            Specifier::Tt(ref name) => {
                matches.insert(name.clone(), Match::Sequence(vec![]));
            },
            _ => { },
        }
    }

    let mut first = true;

    loop {
        if let Some(ref separator) = *separator {
            if !first && parser.apply(|p| p.eat(separator)).ok().map_or(true, |b| !b) {
                return Ok(());
            }
        }

        let mut submatches = HashMap::new();

        parser.start();

        match parse_arguments_(span, parser, &specification, &mut submatches) {
            Ok(()) => { },
            Err(error) => if (first && required) || (!first && separator.is_some()) {
                return Err(error);
            } else {
                parser.rollback();
                return Ok(());
            },
        }

        for (k, v) in submatches {
            match *matches.entry(k).or_insert_with(|| Match::Sequence(vec![])) {
                Match::Sequence(ref mut sequence) => sequence.push(v),
                _ => unreachable!(),
            }
        }

        if amount == Amount::ZeroOrOne {
            return Ok(());
        }

        first = false;
    }
}

fn parse_arguments_<'a>(
    span: Span,
    parser: &mut TransactionParser<'a>,
    specification: &[Specifier],
    matches: &mut HashMap<String, Match>,
) -> PluginResult<()> {
    macro_rules! expect {
        () => ({
            match parser.apply(|p| p.bump_and_get()) {
                Ok(token) => token,
                Err(_) => return span.as_error("unexpected end of arguments"),
            }
        });

        ($expected:expr) => ({
            let expected = $expected;
            let found = expect!();

            if !found.mtwt_eq(expected) {
                let expected = Parser::token_to_string(expected);
                let found = Parser::token_to_string(&found);
                let error = format!("expected `{}`, found `{}`", expected, found);
                return parser.get_last_span().as_error(error);
            }
        });
    }

    macro_rules! try_parse {
        ($method:ident) => (try_parse!($method()));

        ($method:ident($($argument:expr), *)) => ({
            match parser.apply(|p| p.$method($($argument), *)) {
                Ok(ok) => ok,
                Err(_) => return Err(ERROR.with(|e| e.borrow().clone())),
            }
        });
    }

    for specifier in specification {
        match *specifier {
            Specifier::Attr(ref name) => {
                matches.insert(name.clone(), Match::Attr(try_parse!(parse_attribute(true))));
            },
            Specifier::BinOp(ref name) => match expect!() {
                Token::BinOp(binop) | Token::BinOpEq(binop) => {
                    matches.insert(name.clone(), Match::BinOp(binop));
                },
                invalid => {
                    let string = Parser::token_to_string(&invalid);
                    let error = format!("expected binop, found `{}`", string);
                    return parser.get_last_span().as_error(error);
                },
            },
            Specifier::Block(ref name) => {
                matches.insert(name.clone(), Match::Block(try_parse!(parse_block)));
            },
            Specifier::Delim(ref name) => {
                let (delimiter, open) = match expect!() {
                    Token::OpenDelim(delimiter) => (delimiter, parser.get_last_span()),
                    invalid => {
                        let string = Parser::token_to_string(&invalid);
                        let error = format!("expected opening delimiter, found `{}`", string);
                        return parser.get_last_span().as_error(error);
                    },
                };

                let sep = SeqSep { sep: None, trailing_sep_allowed: false };
                let f = |p: &mut Parser| { p.parse_token_tree() };
                let tts = try_parse!(parse_seq_to_end(&Token::CloseDelim(delimiter), sep, f));

                let delimited = Delimited {
                    delim: delimiter, open_span: open, tts: tts, close_span: parser.get_last_span()
                };

                matches.insert(name.clone(), Match::Delim(Rc::new(delimited)));
            },
            Specifier::Expr(ref name) => {
                matches.insert(name.clone(), Match::Expr(try_parse!(parse_expr)));
            },
            Specifier::Ident(ref name) => {
                matches.insert(name.clone(), Match::Ident(try_parse!(parse_ident)));
            },
            Specifier::Item(ref name) => match try_parse!(parse_item) {
                Some(item) => {
                    matches.insert(name.clone(), Match::Item(item));
                },
                None => return parser.get_last_span().as_error("expected item"),
            },
            Specifier::Lftm(ref name) => {
                matches.insert(name.clone(), Match::Lftm(try_parse!(parse_lifetime).name));
            },
            Specifier::Lit(ref name) => {
                matches.insert(name.clone(), Match::Lit(try_parse!(parse_lit)));
            },
            Specifier::Meta(ref name) => {
                matches.insert(name.clone(), Match::Meta(try_parse!(parse_meta_item)));
            },
            Specifier::Pat(ref name) => {
                matches.insert(name.clone(), Match::Pat(try_parse!(parse_pat)));
            },
            Specifier::Path(ref name) => {
                let path = try_parse!(parse_path(PathParsingMode::LifetimeAndTypesWithoutColons));
                matches.insert(name.clone(), Match::Path(path));
            },
            Specifier::Stmt(ref name) => match try_parse!(parse_stmt) {
                Some(item) => {
                    matches.insert(name.clone(), Match::Stmt(item));
                },
                None => return parser.get_last_span().as_error("expected statement"),
            },
            Specifier::Ty(ref name) => {
                matches.insert(name.clone(), Match::Ty(try_parse!(parse_ty)));
            },
            Specifier::Tok(ref name) => {
                matches.insert(name.clone(), Match::Tok(expect!()));
            },
            Specifier::Tt(ref name) => {
                matches.insert(name.clone(), Match::Tt(try_parse!(parse_token_tree)));
            },
            Specifier::Specific(ref expected) => expect!(expected),
            Specifier::Delimited(delimiter, ref subspecification) => {
                expect!(&Token::OpenDelim(delimiter));
                try!(parse_arguments_(span, parser, &subspecification, matches));
                expect!(&Token::CloseDelim(delimiter));
            },
            Specifier::Sequence(amount, ref separator, ref subspecification) => {
                try!(parse_sequence(span, parser, amount, separator, subspecification, matches));
            },
        }
    }

    Ok(())
}

/// Parses the given arguments with the given specification.
pub fn parse_arguments(
    tts: &[TokenTree], specification: &[Specifier]
) -> PluginResult<HashMap<String, Match>> {
    let start = tts.iter().nth(0).map_or(DUMMY_SP, |s| s.get_span());
    let end = tts.iter().last().map_or(DUMMY_SP, |s| s.get_span());
    let span = Span { lo: start.lo, hi: end.hi, expn_id: start.expn_id };

    if !tts.is_empty() && specification.is_empty() {
        return span.as_error("too many arguments");
    }

    let handler = Handler::with_emitter(false, Box::new(SaveEmitter));
    let session = ParseSess::with_span_handler(SpanHandler::new(handler, CodeMap::new()));
    let mut parser = TransactionParser::new(&session, tts);

    let mut matches = HashMap::new();
    try!(parse_arguments_(span, &mut parser, specification, &mut matches));

    if tts.iter().last().map_or(true, |tt| tt.get_span().hi == parser.get_last_span().hi) {
        Ok(matches)
    } else {
        span.as_error("too many arguments")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::collections::{HashMap};

    use syntax::parse;
    use syntax::ast::*;
    use syntax::parse::{ParseSess};
    use syntax::parse::token::{BinOpToken, DelimToken};

    fn parse_token_trees(source: &str) -> Vec<TokenTree> {
        let session = ParseSess::new();
        let source = source.into();
        let mut parser = parse::new_parser_from_source_str(&session, vec![], "".into(), source);
        parser.parse_all_token_trees().unwrap()
    }

    fn with_matches<F>(
        arguments: &str, specification: &str, f: F
    ) where F: Fn(HashMap<String, Match>) {
        let arguments = parse_token_trees(arguments);
        let specification = super::super::parse_specification(&parse_token_trees(specification));
        f(parse_arguments(&arguments, specification.as_ref().unwrap()).unwrap());
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
    }
}
