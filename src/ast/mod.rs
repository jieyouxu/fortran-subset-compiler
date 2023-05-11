use crate::span::{Ident, Span};

pub use string_interner::symbol::SymbolU32 as InternedString;

#[derive(Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl std::fmt::Debug for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Token({:?}, {:?})", &self.kind, &self.span)
    }
}

impl Token {
    pub fn dummy() -> Self {
        Self {
            kind: TokenKind::Dummy,
            span: Span::new(0, 0),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum TokenKind {
    Id(InternedString),
    Lit(Lit),
    Subroutine,
    LParen,
    RParen,
    End,
    Function,
    Comma,
    Integer,
    DoublePrecision,
    Do,
    Eq,
    EndDo,
    If,
    Then,
    EndIf,
    Else,
    Elsif,
    Neq,
    Less,
    Leq,
    Greater,
    Geq,
    Plus,
    Minus,
    Or,
    Mul,
    Div,
    Mod,
    And,
    Period,
    Assign,
    Dummy,
}

#[derive(Copy, Clone, PartialEq)]
pub struct Lit {
    pub kind: LitKind,
    pub symbol: InternedString,
}

impl std::fmt::Debug for Lit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Lit({:?}, {:?})", self.kind, self.symbol)
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum LitKind {
    Double(f64),
    Integer(i64),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Program {
    pub items: Vec<Item>,
    pub span: Span,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Item {
    pub kind: ItemKind,
    pub span: Span,
}

#[derive(Debug, PartialEq, Clone)]
pub enum ItemKind {
    Procedure(Procedure),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Procedure {
    pub ident: Ident,
    pub ret_ty: RetTy,
    pub params: Vec<Ident>,
    pub decls: Vec<Decl>,
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

#[derive(PartialEq, Clone)]
pub struct RetTy {
    pub kind: RetTyKind,
    pub span: Span,
}

impl std::fmt::Debug for RetTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RetTy({:?}, {:?})", self.kind, self.span)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum RetTyKind {
    Integer,
    Double,
    Unit,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Decl {
    pub ident: Ident,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Name {
    pub ident: Ident,
    pub bounds: Option<Vec<Ident>>,
}

#[derive(Debug, PartialEq, Clone)]
pub enum ScalarTy {
    Double,
    Integer,
}

#[derive(PartialEq, Clone)]
pub enum Ty {
    Scalar(ScalarTy),
    Array { base: ScalarTy, bounds: Vec<Expr> },
}

impl std::fmt::Debug for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Scalar(ty) => write!(f, "Ty::Scalar({:?})", ty),
            Self::Array { base, bounds } => {
                write!(f, "Ty::Array(base={:?}, bounds={:?})", base, bounds)
            }
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Debug, PartialEq, Clone)]
pub enum StmtKind {
    DoLoop(DoLoop),
    Assign(Assign),
    If(IfStmt),
}

#[derive(Debug, PartialEq, Clone)]
pub struct DoLoop {
    pub ident: Ident,
    pub lower_bound: Expr,
    pub upper_bound: Expr,
    pub step: Option<Expr>,
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Assign {
    pub lhs: Expr,
    pub rhs: Expr,
    pub span: Span,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug, PartialEq, Clone)]
pub enum ExprKind {
    IntConst(i64),
    DoubleConst(f64),
    Fetch(Ident),
    CallOrIndex { target: Ident, args: Vec<Expr> },
    Unary(UnOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
}

#[derive(Debug, PartialEq, Clone)]
pub enum UnOp {
    Neg,
    Plus,
    Minus,
}

#[derive(Debug, PartialEq, Clone)]
pub enum BinOp {
    Greater,
    Less,
    Geq,
    Leq,
    And,
    Or,
    Eq,
    Neq,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

#[derive(Debug, PartialEq, Clone)]
pub struct IfStmt {
    pub cond: Expr,
    pub if_stmts: Vec<Stmt>,
    pub elsif_stmts: Vec<ElsifStmt>,
    pub else_stmts: Vec<Stmt>,
    pub span: Span,
}

#[derive(Debug, PartialEq, Clone)]
pub struct ElsifStmt {
    pub cond: Expr,
    pub stmts: Vec<Stmt>,
    pub span: Span,
}
