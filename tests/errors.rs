use easy_plugin;

use syntax::codemap::{BytePos};
use syntax::ext::base::{DummyMacroLoader, ExtCtxt};
use syntax::ext::expand::{ExpansionConfig};
use syntax::ext::quote::rt::{ExtParseUtils};
use syntax::parse::{ParseSess};

macro_rules! assert_error_eq {
    ($specification:expr, $lo:expr, $hi:expr, $source:expr, $message:expr) => ({
        let lo = BytePos($lo);
        let hi = BytePos($hi);
        let session = ParseSess::new();
        let config = ExpansionConfig::default("".into());
        let mut loader = DummyMacroLoader;
        let context = ExtCtxt::new(&session, vec![], config, &mut loader);
        let tts = context.parse_tts($source.into());
        match easy_plugin::parse_args(&session, &tts, $specification) {
            Err((span, message)) => if span.lo != lo || span.hi != hi || message != $message {
                println!("\n= Expected =========");
                println!("{:?}, {:?}: {:?}", lo, hi, $message);
                println!("= Generated ========");
                println!("{:?}, {:?}: {:?}", span.lo, span.hi, message);
                panic!();
            },
            _ => panic!("expected error"),
        }
    });
}

#[test]
fn test_errors() {
    let spec = parse_spec!();
    assert_error_eq!(&spec, 0, 3, "322", "too many arguments");
    assert_error_eq!(&spec, 0, 7, "322 644", "too many arguments");

    macro_rules! assert_errors_eq {
        ($spec:expr, $ty:expr, $valid:expr) => ({
            let spec = $spec;
            assert_error_eq!(&spec, 0, 0, "", concat!("expected ", $ty, ": 'a'"));
            assert_error_eq!(&spec, 0, 1, "!", concat!("expected ", $ty, ": 'a'"));
            let start = ($valid.len() as u32) + 1;
            assert_error_eq!(&spec, start, start + 1, concat!($valid, " !"), "too many arguments");
        });
    }

    assert_errors_eq!(parse_spec!($a:attr), "attribute", "#[cfg(test)]");
    assert_errors_eq!(parse_spec!($a:binop), "binary operator", "+");
    assert_errors_eq!(parse_spec!($a:block), "block", "{ let a = 322; }");
    assert_errors_eq!(parse_spec!($a:delim), "opening delimiter", "(1, 2, 3)");
    assert_errors_eq!(parse_spec!($a:expr), "expression", "2 + 2");
    assert_errors_eq!(parse_spec!($a:ident), "identifier", "a");
    assert_errors_eq!(parse_spec!($a:item), "item", "struct A;");
    assert_errors_eq!(parse_spec!($a:lftm), "lifetime", "'a");
    assert_errors_eq!(parse_spec!($a:lit), "literal", "322");
    assert_errors_eq!(parse_spec!($a:meta), "meta item", "cfg(test)");
    assert_errors_eq!(parse_spec!($a:pat), "pattern", "_");
    assert_errors_eq!(parse_spec!($a:path), "path", "::std::path::Path");
    assert_errors_eq!(parse_spec!($a:stmt), "statement", "let a = 322");
    assert_errors_eq!(parse_spec!($a:ty), "type", "(i32, f32)");

    assert_error_eq!(&parse_spec!($a:tok), 0, 0, "", "expected token: 'a'");
    assert_error_eq!(&parse_spec!($a:tt), 0, 0, "", "expected token tree: 'a'");

    let spec = parse_spec!(?);
    assert_error_eq!(&spec, 0, 0, "", "expected `?`");
    assert_error_eq!(&spec, 0, 1, "!", "expected `?`");
    assert_error_eq!(&spec, 1, 2, "?!", "too many arguments");

    let spec = parse_spec!(($a:ident));
    assert_error_eq!(&spec, 0, 0, "", "expected `(`");
    assert_error_eq!(&spec, 0, 1, "!", "expected `(`");
    assert_error_eq!(&spec, 2, 3, "(a!)", "expected `)`");
    assert_error_eq!(&spec, 3, 4, "(a)!", "too many arguments");

    let spec = parse_spec!($($a:ident)+);
    assert_error_eq!(&spec, 0, 0, "", "expected identifier: 'a'");
    assert_error_eq!(&spec, 1, 2, "a!", "too many arguments");
    assert_error_eq!(&spec, 3, 4, "a b!", "too many arguments");

    let spec = parse_spec!($($a:ident)*);
    assert_error_eq!(&spec, 1, 2, "a!", "too many arguments");
    assert_error_eq!(&spec, 3, 4, "a b!", "too many arguments");

    assert_error_eq!(&parse_spec!($($a:ident)?), 2, 3, "a b", "too many arguments");
}
