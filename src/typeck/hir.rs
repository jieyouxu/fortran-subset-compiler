use crate::span::{Ident, Span};
use crate::types::{DeclId, TypeId};

#[derive(Copy, Clone, PartialEq)]
pub struct IntConst(i64);

#[derive(Copy, Clone, PartialEq)]
pub struct DoubleConst(f64);

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
    pub sig: TypeId,
    pub name: Ident,
    pub params: Vec<DeclId>,
    pub decls: Vec<DeclId>,
    pub stmts: Vec<Stmt>,
    pub span: Span,
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
    pub ty: TypeId,
}

#[derive(Debug, PartialEq, Clone)]
pub enum ExprKind {
    IntConst(i64),
    DoubleConst(f64),
    Fetch(DeclId),
    Call { target: DeclId, args: Vec<Expr> },
    Index { target: DeclId, args: Vec<Expr> },
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
