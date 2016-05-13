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

//! Conversion of parsing results into other AST entities.

use std::rc::{Rc};

use syntax::abi::{Abi};
use syntax::ast::*;
use syntax::attr::{ThinAttributes};
use syntax::codemap::{Span, Spanned};
use syntax::parse::token::{self, BinOpToken, DelimToken, Nonterminal};
use syntax::parse::token::{SpecialMacroVar, Token};
use syntax::ptr::{P};

use super::{PluginResult};

//================================================
// Functions
//================================================

convert!(attr: Attribute(attr.node.value.node) -> MetaItemKind, [
    Word(ts) -> (String),
    List(ts, _) -> (String, Vec<P<MetaItem>>),
    NameValue(ts, _) -> (String, Lit),
]);

convert!(expr: Expr(expr.node) -> ExprKind, [
    Box(_) -> (P<Expr>),
    InPlace(_, _) -> (P<Expr>, P<Expr>),
    Vec(_) -> (Vec<P<Expr>>),
    Call(_, _) -> (P<Expr>, Vec<P<Expr>>),
    MethodCall(_, _, _) -> (SpannedIdent, Vec<P<Ty>>, Vec<P<Expr>>),
    Tup(_) -> (Vec<P<Expr>>),
    Binary(_, _, _) -> (BinOp, P<Expr>, P<Expr>),
    Unary(_, _) -> (UnOp, P<Expr>),
    Lit(_) -> (P<Lit>),
    Cast(_, _) -> (P<Expr>, P<Ty>),
    Type(_, _) -> (P<Expr>, P<Ty>),
    If(_, _, _) -> (P<Expr>, P<Block>, Option<P<Expr>>),
    IfLet(_, _, _, _) -> (P<Pat>, P<Expr>, P<Block>, Option<P<Expr>>),
    While(_, _, _) -> (P<Expr>, P<Block>, Option<Ident>),
    WhileLet(_, _, _, _) -> (P<Pat>, P<Expr>, P<Block>, Option<Ident>),
    ForLoop(_, _, _, _) -> (P<Pat>, P<Expr>, P<Block>, Option<Ident>),
    Loop(_, _) -> (P<Block>, Option<Ident>),
    Match(_, _) -> (P<Expr>, Vec<Arm>),
    Closure(_, _, _, _) -> (CaptureBy, P<FnDecl>, P<Block>, Span),
    Block(_) -> (P<Block>),
    Assign(_, _) -> (P<Expr>, P<Expr>),
    AssignOp(_, _, _) -> (BinOp, P<Expr>, P<Expr>),
    Field(_, _) -> (P<Expr>, SpannedIdent),
    TupField(_, _) -> (P<Expr>, Spanned<usize>),
    Index(_, _) -> (P<Expr>, P<Expr>),
    Range(_, _, _) -> (Option<P<Expr>>, Option<P<Expr>>, RangeLimits),
    Path(_, _) -> (Option<QSelf>, Path),
    AddrOf(_, _) -> (Mutability, P<Expr>),
    Break(_) -> (Option<SpannedIdent>),
    Again(_) -> (Option<SpannedIdent>),
    Ret(_) -> (Option<P<Expr>>),
    InlineAsm(_) -> (InlineAsm),
    Mac(_) -> (Mac),
    Struct(_, _, _) -> (Path, Vec<Field>, Option<P<Expr>>),
    Repeat(_, _) -> (P<Expr>, P<Expr>),
    Paren(_) -> (P<Expr>),
    Try(_) -> (P<Expr>),
]);

convert!(item: Item(item.node) -> ItemKind, [
    ExternCrate(masts) -> (Option<String>),
    Use(_) -> (P<ViewPath>),
    Static(_, _, _) -> (P<Ty>, Mutability, P<Expr>),
    Const(_, _) -> (P<Ty>, P<Expr>),
    Fn(_, _, _, _, _, _) -> (P<FnDecl>, Unsafety, Constness, Abi, Generics, P<Block>),
    Mod(_) -> (Mod),
    ForeignMod(_) -> (ForeignMod),
    Ty(_, _) -> (P<Ty>, Generics),
    Enum(_, _) -> (EnumDef, Generics),
    Struct(_, _) -> (VariantData, Generics),
    Trait(_, _, _, _) -> (Unsafety, Generics, TyParamBounds, Vec<TraitItem>),
    DefaultImpl(_, _) -> (Unsafety, TraitRef),
    Impl(_, _, _, _, _, _) -> (Unsafety, ImplPolarity, Generics, Option<TraitRef>, P<Ty>, Vec<ImplItem>),
    Mac(_) -> (Mac),
]);

convert!(lit: Lit(lit.node) -> LitKind, [
    Str(ts, _) -> (String, StrStyle),
    ByteStr(_) -> (Rc<Vec<u8>>),
    Byte(_) -> (u8),
    Char(_) -> (char),
    Int(_, _) -> (u64, LitIntType),
    Float(ts, _) -> (String, FloatTy),
    FloatUnsuffixed(ts) -> (String),
    Bool(_) -> (bool),
]);

convert!(meta: MetaItem(meta.node) -> MetaItemKind, [
    Word(ts) -> (String),
    List(ts, _) -> (String, Vec<P<MetaItem>>),
    NameValue(ts, _) -> (String, Lit),
]);

convert!(pat: Pat(pat.node) -> PatKind, [
    Wild() -> (),
    Ident(_, _, _) -> (BindingMode, SpannedIdent, Option<P<Pat>>),
    Struct(_, _, _) -> (Path, Vec<Spanned<FieldPat>>, bool),
    TupleStruct(_, _) -> (Path, Option<Vec<P<Pat>>>),
    Path(_) -> (Path),
    QPath(_, _) -> (QSelf, Path),
    Tup(_) -> (Vec<P<Pat>>),
    Box(_) -> (P<Pat>),
    Ref(_, _) -> (P<Pat>, Mutability),
    Lit(_) -> (P<Expr>),
    Range(_, _) -> (P<Expr>, P<Expr>),
    Vec(_, _, _) -> (Vec<P<Pat>>, Option<P<Pat>>, Vec<P<Pat>>),
    Mac(_) -> (Mac),
]);

convert!(stmt: Stmt(stmt.node) -> StmtKind, [
    Decl(_, _) -> (P<Decl>, NodeId),
    Expr(_, _) -> (P<Expr>, NodeId),
    Semi(_, _) -> (P<Expr>, NodeId),
    Mac(_, _, _) -> (P<Mac>, MacStmtStyle, ThinAttributes),
]);

convert!(ty: Ty(ty.node) -> TyKind, [
    Vec(_) -> (P<Ty>),
    FixedLengthVec(_, _) -> (P<Ty>, P<Expr>),
    Ptr(_) -> (MutTy),
    Rptr(_, _) -> (Option<Lifetime>, MutTy),
    BareFn(_) -> (P<BareFnTy>),
    Tup(_) -> (Vec<P<Ty>>),
    Path(_, _) -> (Option<QSelf>, Path),
    ObjectSum(_, _) -> (P<Ty>, TyParamBounds),
    PolyTraitRef(_) -> (TyParamBounds),
    Paren(_) -> (P<Ty>),
    Typeof(_) -> (P<Expr>),
    Infer() -> (),
    Mac(_) -> (Mac),
]);

convert!(tok: [Spanned<Token>](tok.node) -> Token, [
    Eq() -> (),
    Lt() -> (),
    Le() -> (),
    EqEq() -> (),
    Ne() -> (),
    Ge() -> (),
    Gt() -> (),
    AndAnd() -> (),
    OrOr() -> (),
    Not() -> (),
    Tilde() -> (),
    BinOp(_) -> (BinOpToken),
    BinOpEq(_) -> (BinOpToken),
    At() -> (),
    Dot() -> (),
    DotDot() -> (),
    DotDotDot() -> (),
    Comma() -> (),
    Semi() -> (),
    Colon() -> (),
    ModSep() -> (),
    RArrow() -> (),
    LArrow() -> (),
    FatArrow() -> (),
    Pound() -> (),
    Dollar() -> (),
    Question() -> (),
    OpenDelim(_) -> (DelimToken),
    CloseDelim(_) -> (DelimToken),
    Literal(_, masts) -> (token::Lit, Option<String>),
    Ident(_) -> (Ident),
    Underscore() -> (),
    Lifetime(_) -> (Ident),
    Interpolated(_) -> (Nonterminal),
    DocComment(asts) -> (String),
    MatchNt(_, _) -> (Ident, Ident),
    SubstNt(_) -> (Ident),
    SpecialVarNt(_) -> (SpecialMacroVar),
    Whitespace() -> (),
    Comment() -> (),
    Shebang(asts) -> (String),
    Eof() -> (),
]);

convert!(tt: TokenTree(*tt) -> TokenTree, [
    Token(_, _) -> (Span, Token),
    Delimited(_, _) -> (Span, Rc<Delimited>),
    Sequence(_, _) -> (Span, Rc<SequenceRepetition>),
]);
