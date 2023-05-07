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
    Bool(bool),
    Integer(i64),
}
