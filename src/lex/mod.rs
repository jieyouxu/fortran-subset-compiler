use std::num::ParseIntError;
use std::ops::Range;

use logos::Logos;
use string_interner::StringInterner;
use strum::AsRefStr;

use crate::ast::{Lit, LitKind, Token, TokenKind};
use crate::span::Span;

#[derive(Debug, Clone, PartialEq, Default)]
pub struct LexerError<'src> {
    pub span: Span,
    pub source: &'src str,
    pub kind: LexerErrorKind,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub enum LexerErrorKind {
    #[default]
    UnexpectedToken,
    ParseIntError(ParseIntError),
}

#[derive(Debug, PartialEq, Clone, Logos, AsRefStr)]
#[logos(skip r"[ \t\n\f]+")]
enum LogosToken<'a> {
    #[regex("[a-zA-Z][a-zA-Z0-9]*")]
    Id(&'a str),
    #[regex("[0-9]+")]
    Lit(&'a str),
    #[token("SUBROUTINE")]
    Subroutine,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("END")]
    End,
    #[token("FUNCTION")]
    Function,
    #[token(",")]
    Comma,
    #[token("INTEGER")]
    Integer,
    #[token("DOUBLE PRECISION")]
    DoublePrecision,
    #[token("DO")]
    Do,
    #[token("=")]
    Eq,
    #[token("ENDDO")]
    EndDo,
    #[token("IF")]
    If,
    #[token("THEN")]
    Then,
    #[token("ENDIF")]
    EndIf,
    #[token("ELSE")]
    Else,
    #[token("ELSIF")]
    Elsif,
    #[token("!=")]
    Neq,
    #[token("<")]
    Less,
    #[token("<=")]
    Leq,
    #[token(".GT.")]
    Greater,
    #[token(">=")]
    Geq,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token(".OR.")]
    Or,
    #[token("*")]
    Mul,
    #[token("/")]
    Div,
    #[token("%")]
    Mod,
    #[token(".AND.")]
    And,
    #[token(".")]
    Period,
}

macro_rules! token {
    ($e: expr, $r: expr) => {
        Token {
            kind: $e,
            span: {
                let Range { start, end } = $r;
                Span::new(start, end)
            },
        }
    };
}

fn parse_int(src: &str, range: std::ops::Range<usize>) -> Result<i64, LexerError<'_>> {
    match i64::from_str_radix(src, 10) {
        Ok(val) => Ok(val),
        Err(e) => Err(LexerError {
            span: Span::new(range.start, range.end),
            source: src,
            kind: LexerErrorKind::ParseIntError(e),
        }),
    }
}

pub fn lex<'src>(
    interner: &mut StringInterner,
    input: &'src str,
) -> Result<Vec<Token>, LexerError<'src>> {
    let mut lexer = LogosToken::lexer(input);
    let tokens = {
        let mut tokens = Vec::new();
        while let Some(result) = lexer.next() {
            match result {
                Ok(logos_token) => {
                    let token = match logos_token {
                        LogosToken::Id(name) => {
                            token!(TokenKind::Id(interner.get_or_intern(name)), lexer.span())
                        }
                        LogosToken::Lit(val) => token!(
                            TokenKind::Lit(Lit {
                                kind: LitKind::Integer(parse_int(val, lexer.span())?),
                                symbol: interner.get_or_intern(val)
                            }),
                            lexer.span()
                        ),
                        LogosToken::Mul => token!(TokenKind::Mul, lexer.span()),
                        LogosToken::Div => token!(TokenKind::Div, lexer.span()),
                        LogosToken::Mod => token!(TokenKind::Mod, lexer.span()),
                        LogosToken::And => token!(TokenKind::And, lexer.span()),
                        LogosToken::Or => token!(TokenKind::Or, lexer.span()),
                        LogosToken::Eq => token!(TokenKind::Eq, lexer.span()),
                        LogosToken::Less => token!(TokenKind::Less, lexer.span()),
                        LogosToken::Leq => token!(TokenKind::Leq, lexer.span()),
                        LogosToken::Greater => token!(TokenKind::Greater, lexer.span()),
                        LogosToken::Geq => token!(TokenKind::Geq, lexer.span()),
                        LogosToken::Comma => token!(TokenKind::Comma, lexer.span()),
                        LogosToken::RParen => token!(TokenKind::RParen, lexer.span()),
                        LogosToken::Then => token!(TokenKind::Then, lexer.span()),
                        LogosToken::Do => token!(TokenKind::Do, lexer.span()),
                        LogosToken::LParen => token!(TokenKind::LParen, lexer.span()),
                        LogosToken::End => token!(TokenKind::End, lexer.span()),
                        LogosToken::Else => token!(TokenKind::Else, lexer.span()),
                        LogosToken::Elsif => token!(TokenKind::Elsif, lexer.span()),
                        LogosToken::If => token!(TokenKind::If, lexer.span()),
                        LogosToken::Subroutine => token!(TokenKind::Subroutine, lexer.span()),
                        LogosToken::Function => token!(TokenKind::Function, lexer.span()),
                        LogosToken::Integer => token!(TokenKind::Integer, lexer.span()),
                        LogosToken::DoublePrecision => {
                            token!(TokenKind::DoublePrecision, lexer.span())
                        }
                        LogosToken::EndDo => token!(TokenKind::EndDo, lexer.span()),
                        LogosToken::EndIf => token!(TokenKind::EndIf, lexer.span()),
                        LogosToken::Neq => token!(TokenKind::Neq, lexer.span()),
                        LogosToken::Plus => token!(TokenKind::Plus, lexer.span()),
                        LogosToken::Minus => token!(TokenKind::Minus, lexer.span()),
                        LogosToken::Period => token!(TokenKind::Period, lexer.span()),
                    };
                    tokens.push(token);
                }
                Err(_) => {
                    return Err(LexerError {
                        span: {
                            let Range { start, end } = lexer.span();
                            Span::new(start, end)
                        },
                        source: lexer.slice(),
                        kind: LexerErrorKind::UnexpectedToken,
                    });
                }
            };
        }
        tokens
    };
    Ok(tokens)
}
