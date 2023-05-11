use tracing::trace;

use crate::ast::*;
use crate::span::{Ident, Span};

#[derive(Debug, Clone, PartialEq)]
pub struct ParseErr {
    pub span: Span,
    pub kind: ParseErrKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParseErrKind {
    UnexpectedEof,
    UnexpectedKind(TokenKind),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    prev_token: Token,
    token: Token,
}

macro_rules! span_of_vec {
    ($items:ident) => {
        match &$items[..] {
            [] => Span::dummy(),
            [item] => item.span,
            [first, .., last] => Span::new(first.span.lo, last.span.hi),
        }
    };
}

impl Parser {
    #[tracing::instrument(skip(tokens))]
    pub fn new(tokens: Vec<Token>) -> Self {
        let token = if tokens.len() >= 1 {
            tokens[0].clone()
        } else {
            Token::dummy()
        };

        Self {
            tokens,
            pos: 0,
            prev_token: Token::dummy(),
            token,
        }
    }

    fn bump(&mut self) -> Result<(), ParseErr> {
        if self.pos == self.tokens.len() - 1 {
            self.pos += 1;
            self.prev_token = self.token.clone();
            self.token = Token::dummy();
            Ok(())
        } else if self.pos < self.tokens.len() - 1 {
            self.pos += 1;
            self.prev_token = self.token.clone();
            self.token = self.tokens[self.pos].clone();
            Ok(())
        } else {
            Err(ParseErr {
                span: self.prev_token.span,
                kind: ParseErrKind::UnexpectedEof,
            })
        }
    }

    fn expect(&mut self, t: &TokenKind) -> Result<Token, ParseErr> {
        if self.token.kind == *t {
            let tok = self.token.clone();
            self.bump()?;
            Ok(tok)
        } else {
            Err(ParseErr {
                span: self.token.span,
                kind: ParseErrKind::UnexpectedKind(self.token.kind),
            })
        }
    }

    pub fn parse_program(&mut self) -> Result<Program, ParseErr> {
        let (items, span) = self.parse_items()?;
        Ok(Program { items, span })
    }

    pub fn parse_items(&mut self) -> Result<(Vec<Item>, Span), ParseErr> {
        let mut items = Vec::new();

        while matches!(
            self.token.kind,
            TokenKind::Integer | TokenKind::DoublePrecision | TokenKind::Subroutine
        ) {
            let item = self.parse_item()?;
            items.push(item);
        }

        let span = span_of_vec!(items);
        Ok((items, span))
    }

    pub fn parse_item(&mut self) -> Result<Item, ParseErr> {
        trace!("parse_item: self.token.kind = {:?}", self.token.kind);
        let procedure = match &self.token.kind {
            // Procedure with return type
            TokenKind::Integer | TokenKind::DoublePrecision => self.parse_function()?,
            // Procedure with unit return type
            TokenKind::Subroutine => self.parse_subroutine()?,
            _ => {
                return Err(ParseErr {
                    span: self.token.span,
                    kind: ParseErrKind::UnexpectedKind(self.token.kind),
                })
            }
        };
        let span = procedure.span;

        Ok(Item {
            kind: ItemKind::Procedure(procedure),
            span,
        })
    }

    pub fn parse_function(&mut self) -> Result<Procedure, ParseErr> {
        trace!("parse function");
        let ret_ty = self.parse_ret_ty()?;
        self.expect(&TokenKind::Function)?;
        let ident = self.parse_ident()?;
        self.expect(&TokenKind::LParen)?;
        let (params, _) = self.parse_formal_params()?;
        self.expect(&TokenKind::RParen)?;
        let (decls, _) = self.parse_decls()?;
        let (stmts, _) = self.parse_stmts()?;
        let end_tok = self.expect(&TokenKind::End)?;

        let span = Span::new(ident.span.lo, end_tok.span.hi);
        Ok(Procedure {
            ident,
            ret_ty,
            params,
            decls,
            stmts,
            span,
        })
    }

    pub fn parse_subroutine(&mut self) -> Result<Procedure, ParseErr> {
        self.expect(&TokenKind::Subroutine)?;
        let ident = self.parse_ident()?;
        self.expect(&TokenKind::LParen)?;
        let (params, _) = self.parse_formal_params()?;
        self.expect(&TokenKind::RParen)?;
        let (decls, _) = self.parse_decls()?;
        let (stmts, _) = self.parse_stmts()?;
        let end_tok = self.expect(&TokenKind::End)?;

        let span = Span::new(ident.span.lo, end_tok.span.hi);
        Ok(Procedure {
            ident,
            ret_ty: RetTy {
                kind: RetTyKind::Unit,
                span: Span::dummy(),
            },
            params,
            decls,
            stmts,
            span,
        })
    }

    pub fn parse_ret_ty(&mut self) -> Result<RetTy, ParseErr> {
        let kind = match &self.token.kind {
            TokenKind::Integer => RetTyKind::Integer,
            TokenKind::DoublePrecision => RetTyKind::Double,
            _ => {
                return Err(ParseErr {
                    span: self.token.span,
                    kind: ParseErrKind::UnexpectedKind(self.token.kind),
                });
            }
        };
        let ret_ty = RetTy {
            kind,
            span: self.token.span,
        };
        self.bump()?;
        Ok(ret_ty)
    }

    pub fn parse_ident(&mut self) -> Result<Ident, ParseErr> {
        match &self.token.kind {
            TokenKind::Id(name) => {
                let ident = Ident {
                    name: *name,
                    span: self.token.span,
                };
                self.bump()?;
                Ok(ident)
            }
            _ => Err(ParseErr {
                span: self.token.span,
                kind: ParseErrKind::UnexpectedKind(self.token.kind),
            }),
        }
    }

    pub fn parse_formal_params(&mut self) -> Result<(Vec<Ident>, Span), ParseErr> {
        if !matches!(self.token.kind, TokenKind::Id(..)) {
            return Ok((vec![], Span::dummy()));
        }

        let mut params = vec![self.parse_ident()?];
        // {, ident}
        while matches!(self.token.kind, TokenKind::Comma) {
            self.expect(&TokenKind::Comma)?;
            let param = self.parse_ident()?;
            params.push(param);
        }

        let span = span_of_vec!(params);
        Ok((params, span))
    }

    pub fn parse_decls(&mut self) -> Result<(Vec<Decl>, Span), ParseErr> {
        let mut decls = Vec::new();
        while matches!(
            self.token.kind,
            TokenKind::Integer | TokenKind::DoublePrecision
        ) {
            let base_ty = match self.token.kind {
                TokenKind::Integer => ScalarTy::Integer,
                TokenKind::DoublePrecision => ScalarTy::Double,
                _ => unreachable!(),
            };
            self.bump()?;

            let (names, _) = self.parse_names(base_ty)?;
            decls.extend(names);
        }

        let span = span_of_vec!(decls);
        Ok((decls, span))
    }

    pub fn parse_names(&mut self, base_ty: ScalarTy) -> Result<(Vec<Decl>, Span), ParseErr> {
        let mut names = vec![self.parse_name(base_ty.clone())?];

        // {, Ident(Ident, Ident)}
        while matches!(self.token.kind, TokenKind::Comma) {
            self.expect(&TokenKind::Comma)?;
            let name = self.parse_name(base_ty.clone())?;
            names.push(name);
        }
        let span = span_of_vec!(names);

        Ok((names, span))
    }

    pub fn parse_name(&mut self, base_ty: ScalarTy) -> Result<Decl, ParseErr> {
        // Ident or Ident(Ident) or Ident(Ident, Ident, ...)
        let ident = self.parse_ident()?;
        let mut span = ident.span;

        let ty = if matches!(self.token.kind, TokenKind::LParen) {
            self.expect(&TokenKind::LParen)?;

            let mut bounds = vec![self.parse_expr()?];
            while matches!(self.token.kind, TokenKind::Comma) {
                self.expect(&TokenKind::Comma)?;
                let expr = self.parse_expr()?;
                bounds.push(expr);
            }

            let rparen_tok = self.expect(&TokenKind::RParen)?;
            span.hi = rparen_tok.span.hi;

            Ty::Array {
                base: base_ty,
                bounds,
            }
        } else {
            Ty::Scalar(base_ty)
        };

        Ok(Decl {
            ident,
            ty,
            span: ident.span,
        })
    }

    pub fn parse_stmts(&mut self) -> Result<(Vec<Stmt>, Span), ParseErr> {
        let mut stmts = Vec::new();

        // FIRST(stmts) = FIRST(stmt)
        //              = FIRST(do_stmt) u FIRST(assign) u FIRST(if_stmt)
        //              = {DO} u FIRST(expr) u {IF}
        //              = {DO, IF} u FIRST(simple_expr)
        //              = {DO, IF} u {+, -} u FIRST(term)
        //              = {DO, IF, +, -} u FIRST(factor)
        //              = {DO, IF, +, -} u {IDENT, INTCONST, (}
        while matches!(
            self.token.kind,
            TokenKind::Do
                | TokenKind::If
                | TokenKind::Plus
                | TokenKind::Minus
                | TokenKind::Id(..)
                | TokenKind::Lit(Lit {
                    kind: LitKind::Integer(..),
                    ..
                })
                | TokenKind::LParen
        ) {
            let stmt = self.parse_stmt()?;
            stmts.push(stmt);
        }

        let span = span_of_vec!(stmts);
        Ok((stmts, span))
    }

    pub fn parse_stmt(&mut self) -> Result<Stmt, ParseErr> {
        let (kind, span) = match self.token.kind {
            TokenKind::Do => {
                let do_loop = self.parse_do_loop()?;
                let span = do_loop.span;
                (StmtKind::DoLoop(do_loop), span)
            }
            TokenKind::If => {
                let if_stmt = self.parse_if_stmt()?;
                let span = if_stmt.span;
                (StmtKind::If(if_stmt), span)
            }
            TokenKind::Plus
            | TokenKind::Minus
            | TokenKind::Id(..)
            | TokenKind::Lit(Lit {
                kind: LitKind::Integer(..),
                ..
            }) => {
                let assign = self.parse_assign()?;
                let span = assign.span;
                (StmtKind::Assign(assign), span)
            }
            _ => {
                return Err(ParseErr {
                    span: self.token.span,
                    kind: ParseErrKind::UnexpectedKind(self.token.kind),
                })
            }
        };

        Ok(Stmt { kind, span })
    }

    pub fn parse_do_loop(&mut self) -> Result<DoLoop, ParseErr> {
        let do_tok = self.expect(&TokenKind::Do)?;
        let ident = self.parse_ident()?;
        self.expect(&TokenKind::Assign)?;
        let lower_bound = self.parse_expr()?;
        self.expect(&TokenKind::Comma)?;
        let upper_bound = self.parse_expr()?;

        let step = if matches!(self.token.kind, TokenKind::Comma) {
            self.expect(&TokenKind::Comma)?;
            Some(self.parse_expr()?)
        } else {
            None
        };

        let (stmts, _) = self.parse_stmts()?;
        let enddo_tok = self.expect(&TokenKind::EndDo)?;
        let span = Span::new(do_tok.span.lo, enddo_tok.span.hi);

        Ok(DoLoop {
            ident,
            lower_bound,
            upper_bound,
            step,
            stmts,
            span,
        })
    }

    pub fn parse_if_stmt(&mut self) -> Result<IfStmt, ParseErr> {
        let if_tok = self.expect(&TokenKind::If)?;
        self.expect(&TokenKind::LParen)?;
        let cond = self.parse_expr()?;
        self.expect(&TokenKind::RParen)?;
        self.expect(&TokenKind::Then)?;
        let (if_stmts, _) = self.parse_stmts()?;
        let (elsif_stmts, _) = self.parse_elsif_stmts()?;
        let else_stmts = if matches!(self.token.kind, TokenKind::Else) {
            self.expect(&TokenKind::Else)?;
            let (stmts, _) = self.parse_stmts()?;
            stmts
        } else {
            vec![]
        };

        let endif_tok = self.expect(&TokenKind::EndIf)?;
        let span = Span::new(if_tok.span.lo, endif_tok.span.hi);

        Ok(IfStmt {
            cond,
            if_stmts,
            elsif_stmts,
            else_stmts,
            span,
        })
    }

    pub fn parse_elsif_stmts(&mut self) -> Result<(Vec<ElsifStmt>, Span), ParseErr> {
        let mut elsif_stmts = Vec::new();

        while matches!(self.token.kind, TokenKind::Elsif) {
            let elsif_stmt = self.parse_elsif_stmt()?;
            elsif_stmts.push(elsif_stmt);
        }

        let span = span_of_vec!(elsif_stmts);
        Ok((elsif_stmts, span))
    }

    pub fn parse_elsif_stmt(&mut self) -> Result<ElsifStmt, ParseErr> {
        let elsif_tok = self.expect(&TokenKind::Elsif)?;
        self.expect(&TokenKind::LParen)?;
        let cond = self.parse_expr()?;
        self.expect(&TokenKind::RParen)?;
        self.expect(&TokenKind::Then)?;
        let (stmts, stmts_span) = self.parse_stmts()?;
        let span = Span::new(elsif_tok.span.lo, stmts_span.hi);

        Ok(ElsifStmt { cond, stmts, span })
    }

    pub fn parse_assign(&mut self) -> Result<Assign, ParseErr> {
        let lhs = self.parse_expr()?;
        self.expect(&TokenKind::Assign)?;
        let rhs = self.parse_expr()?;
        let span = Span::new(lhs.span.lo, rhs.span.hi);

        Ok(Assign { lhs, rhs, span })
    }

    pub fn parse_expr(&mut self) -> Result<Expr, ParseErr> {
        let lhs = self.parse_simple_expr()?;

        if matches!(
            self.token.kind,
            TokenKind::Eq
                | TokenKind::Neq
                | TokenKind::Less
                | TokenKind::Leq
                | TokenKind::Greater
                | TokenKind::Geq
        ) {
            let bin_op = match &self.token.kind {
                TokenKind::Eq => BinOp::Eq,
                TokenKind::Neq => BinOp::Neq,
                TokenKind::Less => BinOp::Less,
                TokenKind::Leq => BinOp::Leq,
                TokenKind::Greater => BinOp::Greater,
                TokenKind::Geq => BinOp::Geq,
                _ => unreachable!(),
            };
            self.bump()?;

            let rhs = self.parse_simple_expr()?;
            let span = Span::new(lhs.span.lo, rhs.span.hi);

            Ok(Expr {
                kind: ExprKind::Binary(bin_op, Box::new(lhs), Box::new(rhs)),
                span,
            })
        } else {
            Ok(lhs)
        }
    }

    pub fn parse_simple_expr(&mut self) -> Result<Expr, ParseErr> {
        let lo = self.token.span.lo;

        let unary_op = match self.token.kind {
            TokenKind::Plus => {
                self.bump()?; // `+`
                Some(UnOp::Plus)
            }
            TokenKind::Minus => {
                self.bump()?; // `-`
                Some(UnOp::Minus)
            }
            _ => None,
        };

        let leftmost = if let Some(unary_op) = unary_op {
            let term = self.parse_term()?;
            let span = Span::new(lo, term.span.hi);

            Expr {
                kind: ExprKind::Unary(unary_op, Box::new(term)),
                span: Span::new(lo, span.hi),
            }
        } else {
            self.parse_term()?
        };

        let expr = if matches!(
            self.token.kind,
            TokenKind::Plus | TokenKind::Minus | TokenKind::Or
        ) {
            let mut pieces = Vec::new();

            while matches!(
                self.token.kind,
                TokenKind::Plus | TokenKind::Minus | TokenKind::Or
            ) {
                let bin_op = match self.token.kind {
                    TokenKind::Plus => BinOp::Add,
                    TokenKind::Minus => BinOp::Sub,
                    TokenKind::Or => BinOp::Or,
                    _ => unreachable!(),
                };
                self.bump()?; // `+` or `-` or `OR`

                let rterm = self.parse_term()?;
                pieces.push(((bin_op), rterm));
            }

            assert!(pieces.len() >= 1);
            build_left_associative_term_tree(leftmost, pieces)
        } else {
            leftmost
        };

        Ok(expr)
    }

    pub fn parse_term(&mut self) -> Result<Expr, ParseErr> {
        let leftmost = self.parse_factor()?;

        let expr = if matches!(
            self.token.kind,
            TokenKind::Mul | TokenKind::Div | TokenKind::Mod | TokenKind::And
        ) {
            let mut pieces = Vec::new();

            while matches!(
                self.token.kind,
                TokenKind::Mul | TokenKind::Div | TokenKind::Mod | TokenKind::And
            ) {
                let bin_op = match self.token.kind {
                    TokenKind::Mul => BinOp::Mul,
                    TokenKind::Div => BinOp::Div,
                    TokenKind::Mod => BinOp::Mod,
                    TokenKind::And => BinOp::And,
                    _ => unreachable!(),
                };
                self.bump()?; // `*` or `DIV` or `MOD` or `&`

                let rfactor = self.parse_factor()?;
                pieces.push((bin_op, rfactor));
            }

            assert!(pieces.len() >= 1);
            build_left_associative_term_tree(leftmost, pieces)
        } else {
            leftmost
        };

        Ok(expr)
    }

    pub fn parse_factor(&mut self) -> Result<Expr, ParseErr> {
        let expr = match self.token.kind {
            TokenKind::Id(..) => {
                let ident = self.parse_ident()?;

                if matches!(self.token.kind, TokenKind::LParen) {
                    // ident ( args )
                    self.expect(&TokenKind::LParen)?;
                    let (args, _) = self.parse_args()?;
                    let rparen_tok = self.expect(&TokenKind::RParen)?;

                    Expr {
                        kind: ExprKind::CallOrIndex {
                            target: ident,
                            args,
                        },
                        span: Span::new(ident.span.lo, rparen_tok.span.hi),
                    }
                } else {
                    Expr {
                        kind: ExprKind::Fetch(ident),
                        span: ident.span,
                    }
                }
            }
            TokenKind::Lit(Lit {
                kind: LitKind::Integer(_) | LitKind::Double(_),
                ..
            }) => self.parse_number()?,
            TokenKind::LParen => {
                let lparen_tok = self.expect(&TokenKind::LParen)?;
                let expr = self.parse_expr()?;
                let rparen_tok = self.expect(&TokenKind::RParen)?;

                Expr {
                    span: Span::new(lparen_tok.span.lo, rparen_tok.span.hi),
                    ..expr
                }
            }
            _ => {
                return Err(ParseErr {
                    span: self.token.span,
                    kind: ParseErrKind::UnexpectedKind(self.token.kind),
                })
            }
        };
        Ok(expr)
    }

    pub fn parse_args(&mut self) -> Result<(Vec<Expr>, Span), ParseErr> {
        let mut args = Vec::new();
        if matches!(
            self.token.kind,
            TokenKind::Plus
                | TokenKind::Minus
                | TokenKind::LParen
                | TokenKind::Id(_)
                | TokenKind::Lit(Lit {
                    kind: LitKind::Integer(_),
                    ..
                })
        ) {
            let expr = self.parse_expr()?;
            args.push(expr);
            while matches!(self.token.kind, TokenKind::Comma) {
                self.expect(&TokenKind::Comma)?;
                let expr = self.parse_expr()?;
                args.push(expr);
            }
        }

        let span = span_of_vec!(args);
        Ok((args, span))
    }

    pub fn parse_number(&mut self) -> Result<Expr, ParseErr> {
        if matches!(
            self.token.kind,
            TokenKind::Lit(Lit {
                kind: LitKind::Integer(..) | LitKind::Double(..),
                ..
            })
        ) {
            let tok = self.token.clone();
            self.bump()?;
            let span = tok.span;
            match tok.kind {
                TokenKind::Lit(Lit {
                    kind: LitKind::Integer(val),
                    ..
                }) => Ok(Expr {
                    kind: ExprKind::IntConst(val),
                    span,
                }),
                TokenKind::Lit(Lit {
                    kind: LitKind::Double(val),
                    ..
                }) => Ok(Expr {
                    kind: ExprKind::DoubleConst(val),
                    span,
                }),
                _ => unreachable!(),
            }
        } else {
            Err(ParseErr {
                span: self.token.span,
                kind: ParseErrKind::UnexpectedKind(self.token.kind),
            })
        }
    }
}

fn build_left_associative_term_tree(leftmost: Expr, pieces: Vec<(BinOp, Expr)>) -> Expr {
    let mut pieces = pieces.clone();
    build_left_associative_term_tree_inner(leftmost, &mut pieces)
}

fn build_left_associative_term_tree_inner(leftmost: Expr, pieces: &mut Vec<(BinOp, Expr)>) -> Expr {
    if pieces.is_empty() {
        leftmost
    } else {
        let (bin_op, rterm) = pieces.pop().unwrap();
        let lhs = build_left_associative_term_tree_inner(leftmost, pieces);
        Expr {
            kind: ExprKind::Binary(bin_op, Box::new(lhs.clone()), Box::new(rterm.clone())),
            span: Span::new(lhs.span.lo, rterm.span.hi),
        }
    }
}
