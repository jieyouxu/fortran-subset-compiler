use crate::ast;
use crate::ast::*;
use crate::session::{Diagnostic, DiagnosticKind, Session};
use crate::span::Ident;
use crate::types::{Decl, DeclId, TyCtxt, Type, TypeId};

use indexmap::IndexMap;
use std::collections::{HashMap, HashSet};
use string_interner::symbol::SymbolU32 as InternedString;
use string_interner::StringInterner;
use tracing::trace;

pub mod hir;

#[derive(Debug)]
struct LexicalScope<'a> {
    kind: LexicalScopeKind,
    names: HashMap<InternedString, DeclId>,
    parent: Option<&'a LexicalScope<'a>>,
}

#[derive(Debug)]
enum LexicalScopeKind {
    Regular,
    Procedure,
    Global,
}

impl<'a> LexicalScope<'a> {
    fn global(interner: &mut StringInterner) -> Self {
        Self {
            kind: LexicalScopeKind::Global,
            // Predefined decls
            names: HashMap::from_iter([(interner.get_or_intern("DABS"), TyCtxt::DABS_DECL_ID)]),
            parent: None,
        }
    }

    fn procedure(parent: &'a LexicalScope<'a>) -> Self {
        Self {
            kind: LexicalScopeKind::Procedure,
            names: Default::default(),
            parent: Some(parent),
        }
    }

    fn try_define(&mut self, name: InternedString, symbol: DeclId) -> Result<InternedString, ()> {
        match self.names.try_insert(name, symbol) {
            Ok(_) => Ok(name),
            Err(_) => Err(()),
        }
    }

    fn lookup(&self, name: InternedString) -> Option<DeclId> {
        let mut current_scope = Some(self);
        while let Some(scope) = current_scope {
            if scope.names.contains_key(&name) {
                return scope.names.get(&name).copied();
            }
            current_scope = scope.parent;
        }

        None
    }
}

pub struct LowerAst<'tcx, 'sess, 'icx> {
    pub tcx: &'tcx mut TyCtxt<'icx>,
    pub sess: &'sess mut Session,
}

impl<'tcx, 'sess, 'icx> LowerAst<'tcx, 'sess, 'icx> {
    pub fn lower_program(&mut self, program: &Program) -> Result<hir::Program, ()> {
        let mut items = Vec::new();
        let mut scope = LexicalScope::global(&mut self.tcx.interner);
        for item in &program.items {
            items.push(self.lower_item(item, &mut scope)?);
        }
        Ok(hir::Program {
            items,
            span: program.span,
        })
    }

    fn lower_item(&mut self, item: &Item, scope: &mut LexicalScope<'_>) -> Result<hir::Item, ()> {
        let kind = match &item.kind {
            ItemKind::Procedure(procedure) => {
                hir::ItemKind::Procedure(self.lower_procedure(procedure, scope)?)
            }
        };
        Ok(hir::Item {
            kind,
            span: item.span,
        })
    }

    fn lower_procedure(
        &mut self,
        procedure: &Procedure,
        scope: &mut LexicalScope<'_>,
    ) -> Result<hir::Procedure, ()> {
        trace!(
            "lower_procedure: procedure = {}",
            self.tcx.interner.resolve(procedure.ident.name).unwrap()
        );
        let ret_ty = self.lower_ret_ty(&procedure.ret_ty)?;
        // Need 2 passes on params: one pass to collect param types and
        // another pass to actually register the params under nested scope.
        let mut dummy_scope = LexicalScope::procedure(scope);
        let params = self.lower_params(&procedure.params, &procedure.decls, &mut dummy_scope)?;
        let param_tys = params.iter().map(|&p| self.tcx.get_decl(p).ty).collect();
        let sig = self.tcx.alloc_type(Type::Procedure {
            params: param_tys,
            ret_ty,
        });
        let procedure_decl = self.tcx.alloc_decl(Decl {
            name: procedure.ident.name,
            ty: sig,
        });

        if scope
            .try_define(procedure.ident.name, procedure_decl)
            .is_err()
        {
            self.sess.emit_diagnostic(Diagnostic {
                kind: DiagnosticKind::DuplicateProcedureDeclaration,
                message: "procedure already defined".to_owned(),
                span: procedure.span,
            });
            return Err(());
        };

        let mut procedure_scope = LexicalScope::procedure(scope);
        let params =
            self.lower_params(&procedure.params, &procedure.decls, &mut procedure_scope)?;
        trace!(?params);
        let decls = self.process_non_param_decls(
            &procedure.decls,
            &procedure.params,
            &mut procedure_scope,
        )?;
        trace!(?decls);
        let stmts = self.lower_stmts(&procedure.stmts, &mut procedure_scope)?;

        trace!(?stmts);

        Ok(hir::Procedure {
            sig,
            name: procedure.ident,
            params,
            decls,
            stmts,
            span: procedure.span,
        })
    }

    fn lower_ret_ty(&mut self, ret_ty: &RetTy) -> Result<TypeId, ()> {
        let ty_id = match ret_ty.kind {
            RetTyKind::Integer => TyCtxt::INTEGER_TYPE_ID,
            RetTyKind::Double => TyCtxt::DOUBLE_TYPE_ID,
            RetTyKind::Unit => TyCtxt::UNIT_TYPE_ID,
        };
        Ok(ty_id)
    }

    fn lower_params(
        &mut self,
        params: &[Ident],
        decls: &[ast::Decl],
        scope: &mut LexicalScope<'_>,
    ) -> Result<Vec<DeclId>, ()> {
        self.check_duplicate_decls(decls)?;
        let mut param_decl_map = HashMap::new();

        // First pass: register the parameters with primitive types.
        for decl in decls {
            for param in params {
                if decl.ident.name == param.name {
                    match &decl.ty {
                        Ty::Scalar(..) => {
                            let ty = self.lower_ty_to_ty(&decl.ty, scope)?;
                            let decl_id = self.tcx.alloc_decl(Decl {
                                name: param.name,
                                ty,
                            });
                            scope.try_define(param.name, decl_id)?;
                            param_decl_map.insert(decl.ident.name, decl_id);
                        }
                        Ty::Array { .. } => {}
                    }
                }
            }
        }

        // Second pass: resolve the parameters with non-primitive types
        for decl in decls {
            for param in params {
                if decl.ident.name == param.name {
                    match &decl.ty {
                        Ty::Array { .. } => {
                            let ty = self.lower_ty_to_ty(&decl.ty, scope)?;
                            let decl_id = self.tcx.alloc_decl(Decl {
                                name: param.name,
                                ty,
                            });
                            scope.try_define(param.name, decl_id)?;
                            param_decl_map.insert(decl.ident.name, decl_id);
                        }
                        Ty::Scalar(..) => {}
                    }
                }
            }
        }

        let mut ordered_param_decl_ids = Vec::new();
        for param in params {
            let decl_id = *param_decl_map.get(&param.name).unwrap();
            ordered_param_decl_ids.push(decl_id);
        }

        Ok(ordered_param_decl_ids)
    }

    fn check_duplicate_decls(&mut self, decls: &[ast::Decl]) -> Result<(), ()> {
        let mut unique_decl_names = HashSet::new();
        for decl in decls {
            if !unique_decl_names.insert(decl.ident.name) {
                self.sess.emit_diagnostic(Diagnostic {
                    kind: DiagnosticKind::DuplicateVariableDeclaration,
                    message: format!(
                        "variable or parameter `{}` already defined",
                        self.tcx.interner.resolve(decl.ident.name).unwrap()
                    ),
                    span: decl.ident.span,
                });
                return Err(());
            }
        }
        Ok(())
    }

    fn lower_ty_to_ty(&mut self, ty: &Ty, scope: &mut LexicalScope<'_>) -> Result<TypeId, ()> {
        let ty_id = match ty {
            Ty::Scalar(s) => match s {
                ScalarTy::Double => TyCtxt::DOUBLE_TYPE_ID,
                ScalarTy::Integer => TyCtxt::INTEGER_TYPE_ID,
            },
            Ty::Array { base, bounds } => {
                let mut exprs = Vec::new();
                for bound in bounds {
                    let expr = self.lower_expr(bound, scope)?;
                    if expr.ty != TyCtxt::INTEGER_TYPE_ID {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::NonIntegerBoundExpr,
                            message: "bound expressions must be of integer type".to_owned(),
                            span: bound.span,
                        });
                        return Err(());
                    }
                    exprs.push(expr);
                }
                self.tcx.alloc_type(Type::Array {
                    base_ty: match base {
                        ScalarTy::Double => TyCtxt::DOUBLE_TYPE_ID,
                        ScalarTy::Integer => TyCtxt::INTEGER_TYPE_ID,
                    },
                    dimensions: exprs.len(),
                })
            }
        };
        Ok(ty_id)
    }

    fn lower_expr(&mut self, expr: &Expr, scope: &mut LexicalScope<'_>) -> Result<hir::Expr, ()> {
        let (kind, ty) = match &expr.kind {
            ExprKind::IntConst(val) => (hir::ExprKind::IntConst(*val), TyCtxt::INTEGER_TYPE_ID),
            ExprKind::DoubleConst(val) => {
                (hir::ExprKind::DoubleConst(*val), TyCtxt::DOUBLE_TYPE_ID)
            }
            ExprKind::Fetch(ident) => {
                let decl = self.lower_ident(*ident, scope)?;
                let ty = self.tcx.get_decl(decl).ty;
                (hir::ExprKind::Fetch(decl), ty)
            }
            ExprKind::CallOrIndex { target, args } => {
                let args = self.lower_args(args, scope)?;
                let target_decl_id = self.lower_call_or_index_ident(*target, scope)?;
                let target_decl = self.tcx.get_decl(target_decl_id);
                let target_ty = self.tcx.get_type(target_decl.ty);

                match &target_ty {
                    Type::Procedure { params, ret_ty } => {
                        trace!(?target_ty);
                        trace!(
                            "param types {:?} => {:?}",
                            params,
                            params
                                .iter()
                                .map(|p| self.tcx.get_type(*p))
                                .collect::<Vec<_>>()
                        );

                        if params.len() != args.len() {
                            self.sess.emit_diagnostic(Diagnostic {
                                kind: DiagnosticKind::ParamArgCountMismatch {
                                    expected: params.len(),
                                    found: args.len(),
                                },
                                message: format!(
                                    "expected {} arguments but found {} arguments",
                                    params.len(),
                                    args.len()
                                ),
                                span: expr.span,
                            });
                            return Err(());
                        }

                        for (param_ty, arg) in params.iter().zip(args.iter()) {
                            if !self.tcx.type_equals(*param_ty, arg.ty) {
                                self.sess.emit_diagnostic(Diagnostic {
                                    kind: DiagnosticKind::ArgumentTypeMismatch {
                                        expected: *param_ty,
                                        found: arg.ty,
                                    },
                                    message: format!(
                                        "expected argument type `{:?}` but found `{:?}`",
                                        self.tcx.get_type(*param_ty),
                                        self.tcx.get_type(arg.ty)
                                    ),
                                    span: arg.span,
                                });
                                return Err(());
                            }
                        }

                        (
                            hir::ExprKind::Call {
                                target: target_decl_id,
                                args,
                            },
                            *ret_ty,
                        )
                    }
                    Type::Array {
                        base_ty,
                        dimensions,
                    } => {
                        if *dimensions != args.len() {
                            self.sess.emit_diagnostic(Diagnostic {
                                kind: DiagnosticKind::ArrayIndexDimensionMismatch {
                                    expected: *dimensions,
                                    found: args.len(),
                                },
                                message: format!(
                                    "array index dimension mismatch: expected `{}` but found `{}`",
                                    *dimensions,
                                    args.len()
                                ),
                                span: expr.span,
                            });
                            return Err(());
                        }

                        for arg in &args {
                            if arg.ty != TyCtxt::INTEGER_TYPE_ID {
                                self.sess.emit_diagnostic(Diagnostic {
                                    kind: DiagnosticKind::NonIntegerIndexExpr,
                                    message: "index expressions must be of integer type".to_owned(),
                                    span: arg.span,
                                });
                                return Err(());
                            }
                        }

                        (
                            hir::ExprKind::Index {
                                target: target_decl_id,
                                args,
                            },
                            *base_ty,
                        )
                    }
                    _ => unreachable!(),
                }
            }
            ExprKind::Unary(un_op, e) => match un_op {
                UnOp::Neg => {
                    let e = self.lower_expr(e, scope)?;
                    if e.ty != TyCtxt::BOOL_TYPE_ID {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::UnexpectedType {
                                expected: TyCtxt::BOOL_TYPE_ID,
                                found: e.ty,
                            },
                            message: "cannot negate a non-bool expression".to_owned(),
                            span: e.span,
                        });
                        return Err(());
                    }

                    (
                        hir::ExprKind::Unary(hir::UnOp::Neg, Box::new(e)),
                        TyCtxt::BOOL_TYPE_ID,
                    )
                }
                UnOp::Plus => {
                    let e = self.lower_expr(e, scope)?;
                    if e.ty != TyCtxt::INTEGER_TYPE_ID {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::UnexpectedType {
                                expected: TyCtxt::INTEGER_TYPE_ID,
                                found: e.ty,
                            },
                            message: format!(
                                "unexpected type: expected int but found `{:?}`",
                                self.tcx.get_type(e.ty)
                            ),
                            span: e.span,
                        });
                        return Err(());
                    }

                    (
                        hir::ExprKind::Unary(hir::UnOp::Plus, Box::new(e)),
                        TyCtxt::INTEGER_TYPE_ID,
                    )
                }
                UnOp::Minus => {
                    let e = self.lower_expr(e, scope)?;
                    if e.ty != TyCtxt::INTEGER_TYPE_ID {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::UnexpectedType {
                                expected: TyCtxt::INTEGER_TYPE_ID,
                                found: e.ty,
                            },
                            message: format!(
                                "unexpected type: expected int but found `{:?}`",
                                self.tcx.get_type(e.ty)
                            ),
                            span: e.span,
                        });
                        return Err(());
                    }

                    (
                        hir::ExprKind::Unary(hir::UnOp::Minus, Box::new(e)),
                        TyCtxt::INTEGER_TYPE_ID,
                    )
                }
            },
            ExprKind::Binary(bin_op, a, b) => match bin_op {
                BinOp::Greater => {
                    let a = self.lower_expr(a, scope)?;
                    let b = self.lower_expr(b, scope)?;
                    if a.ty == TyCtxt::INTEGER_TYPE_ID && b.ty == TyCtxt::INTEGER_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Greater, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty == TyCtxt::DOUBLE_TYPE_ID && b.ty == TyCtxt::DOUBLE_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Greater, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty != b.ty {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::BinOpTypeMismatch {
                                lhs: a.ty,
                                rhs: b.ty,
                            },
                            message: format!(
                                "binary operation LHS expression has type `{:?}` but RHS expression has `{:?}`",
                                self.tcx.get_type(a.ty),
                                self.tcx.get_type(b.ty)
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    } else {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::UnsupportedType {
                                supported: vec![],
                                found: a.ty,
                            },
                            message: format!(
                                "binary operation has unsupported type `{:?}`",
                                self.tcx.get_type(a.ty),
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    }
                }
                BinOp::Less => {
                    let a = self.lower_expr(a, scope)?;
                    let b = self.lower_expr(b, scope)?;
                    if a.ty == TyCtxt::INTEGER_TYPE_ID && b.ty == TyCtxt::INTEGER_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Less, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty == TyCtxt::DOUBLE_TYPE_ID && b.ty == TyCtxt::DOUBLE_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Less, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty != b.ty {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::BinOpTypeMismatch {
                                lhs: a.ty,
                                rhs: b.ty,
                            },
                            message: format!(
                                "binary operation LHS expression has type `{:?}` but RHS expression has `{:?}`",
                                self.tcx.get_type(a.ty),
                                self.tcx.get_type(b.ty)
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    } else {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::UnsupportedType {
                                supported: vec![],
                                found: a.ty,
                            },
                            message: format!(
                                "binary operation has unsupported type `{:?}`",
                                self.tcx.get_type(a.ty),
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    }
                }
                BinOp::Geq => {
                    let a = self.lower_expr(a, scope)?;
                    let b = self.lower_expr(b, scope)?;
                    if a.ty == TyCtxt::INTEGER_TYPE_ID && b.ty == TyCtxt::INTEGER_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Geq, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty == TyCtxt::DOUBLE_TYPE_ID && b.ty == TyCtxt::DOUBLE_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Geq, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty != b.ty {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::BinOpTypeMismatch {
                                lhs: a.ty,
                                rhs: b.ty,
                            },
                            message: format!(
                                "binary operation LHS expression has type `{:?}` but RHS expression has `{:?}`",
                                self.tcx.get_type(a.ty),
                                self.tcx.get_type(b.ty)
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    } else {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::UnsupportedType {
                                supported: vec![],
                                found: a.ty,
                            },
                            message: format!(
                                "binary operation has unsupported type `{:?}`",
                                self.tcx.get_type(a.ty),
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    }
                }
                BinOp::Leq => {
                    let a = self.lower_expr(a, scope)?;
                    let b = self.lower_expr(b, scope)?;
                    if a.ty == TyCtxt::INTEGER_TYPE_ID && b.ty == TyCtxt::INTEGER_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Leq, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty == TyCtxt::DOUBLE_TYPE_ID && b.ty == TyCtxt::DOUBLE_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Leq, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty != b.ty {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::BinOpTypeMismatch {
                                lhs: a.ty,
                                rhs: b.ty,
                            },
                            message: format!(
                                "binary operation LHS expression has type `{:?}` but RHS expression has `{:?}`",
                                self.tcx.get_type(a.ty),
                                self.tcx.get_type(b.ty)
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    } else {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::UnsupportedType {
                                supported: vec![],
                                found: a.ty,
                            },
                            message: format!(
                                "binary operation has unsupported type `{:?}`",
                                self.tcx.get_type(a.ty),
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    }
                }
                BinOp::And => {
                    let a = self.lower_expr(a, scope)?;
                    let b = self.lower_expr(b, scope)?;
                    if a.ty == TyCtxt::INTEGER_TYPE_ID && b.ty == TyCtxt::INTEGER_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::And, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty == TyCtxt::DOUBLE_TYPE_ID && b.ty == TyCtxt::DOUBLE_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::And, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty == TyCtxt::BOOL_TYPE_ID && b.ty == TyCtxt::BOOL_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::And, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty != b.ty {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::BinOpTypeMismatch {
                                lhs: a.ty,
                                rhs: b.ty,
                            },
                            message: format!(
                                "binary operation LHS expression has type `{:?}` but RHS expression has `{:?}`",
                                self.tcx.get_type(a.ty),
                                self.tcx.get_type(b.ty)
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    } else {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::UnsupportedType {
                                supported: vec![],
                                found: a.ty,
                            },
                            message: format!(
                                "binary operation has unsupported type `{:?}`",
                                self.tcx.get_type(a.ty),
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    }
                }
                BinOp::Or => {
                    let a = self.lower_expr(a, scope)?;
                    let b = self.lower_expr(b, scope)?;
                    if a.ty == TyCtxt::INTEGER_TYPE_ID && b.ty == TyCtxt::INTEGER_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Or, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty == TyCtxt::DOUBLE_TYPE_ID && b.ty == TyCtxt::DOUBLE_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Or, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty == TyCtxt::BOOL_TYPE_ID && b.ty == TyCtxt::BOOL_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Or, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty != b.ty {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::BinOpTypeMismatch {
                                lhs: a.ty,
                                rhs: b.ty,
                            },
                            message: format!(
                                "binary operation LHS expression has type `{:?}` but RHS expression has `{:?}`",
                                self.tcx.get_type(a.ty),
                                self.tcx.get_type(b.ty)
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    } else {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::UnsupportedType {
                                supported: vec![],
                                found: a.ty,
                            },
                            message: format!(
                                "binary operation has unsupported type `{:?}`",
                                self.tcx.get_type(a.ty),
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    }
                }
                BinOp::Eq => {
                    let a = self.lower_expr(a, scope)?;
                    let b = self.lower_expr(b, scope)?;
                    if a.ty == TyCtxt::INTEGER_TYPE_ID && b.ty == TyCtxt::INTEGER_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Eq, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty == TyCtxt::DOUBLE_TYPE_ID && b.ty == TyCtxt::DOUBLE_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Eq, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty == TyCtxt::BOOL_TYPE_ID && b.ty == TyCtxt::BOOL_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Eq, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty != b.ty {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::BinOpTypeMismatch {
                                lhs: a.ty,
                                rhs: b.ty,
                            },
                            message: format!(
                                "binary operation LHS expression has type `{:?}` but RHS expression has `{:?}`",
                                self.tcx.get_type(a.ty),
                                self.tcx.get_type(b.ty)
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    } else {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::UnsupportedType {
                                supported: vec![],
                                found: a.ty,
                            },
                            message: format!(
                                "binary operation has unsupported type `{:?}`",
                                self.tcx.get_type(a.ty),
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    }
                }
                BinOp::Neq => {
                    let a = self.lower_expr(a, scope)?;
                    let b = self.lower_expr(b, scope)?;
                    if a.ty == TyCtxt::INTEGER_TYPE_ID && b.ty == TyCtxt::INTEGER_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Neq, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty == TyCtxt::DOUBLE_TYPE_ID && b.ty == TyCtxt::DOUBLE_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Neq, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty == TyCtxt::BOOL_TYPE_ID && b.ty == TyCtxt::BOOL_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Neq, Box::new(a), Box::new(b)),
                            TyCtxt::BOOL_TYPE_ID,
                        )
                    } else if a.ty != b.ty {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::BinOpTypeMismatch {
                                lhs: a.ty,
                                rhs: b.ty,
                            },
                            message: format!(
                                "binary operation LHS expression has type `{:?}` but RHS expression has `{:?}`",
                                self.tcx.get_type(a.ty),
                                self.tcx.get_type(b.ty)
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    } else {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::UnsupportedType {
                                supported: vec![],
                                found: a.ty,
                            },
                            message: format!(
                                "binary operation has unsupported type `{:?}`",
                                self.tcx.get_type(a.ty),
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    }
                }
                BinOp::Add => {
                    let a = self.lower_expr(a, scope)?;
                    let b = self.lower_expr(b, scope)?;
                    if a.ty == TyCtxt::INTEGER_TYPE_ID && b.ty == TyCtxt::INTEGER_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Add, Box::new(a), Box::new(b)),
                            TyCtxt::INTEGER_TYPE_ID,
                        )
                    } else if a.ty == TyCtxt::DOUBLE_TYPE_ID && b.ty == TyCtxt::DOUBLE_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Add, Box::new(a), Box::new(b)),
                            TyCtxt::DOUBLE_TYPE_ID,
                        )
                    } else if a.ty != b.ty {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::BinOpTypeMismatch {
                                lhs: a.ty,
                                rhs: b.ty,
                            },
                            message: format!(
                                "binary operation LHS expression has type `{:?}` but RHS expression has `{:?}`",
                                self.tcx.get_type(a.ty),
                                self.tcx.get_type(b.ty)
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    } else {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::UnsupportedType {
                                supported: vec![],
                                found: a.ty,
                            },
                            message: format!(
                                "binary operation has unsupported type `{:?}`",
                                self.tcx.get_type(a.ty),
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    }
                }
                BinOp::Sub => {
                    let a = self.lower_expr(a, scope)?;
                    let b = self.lower_expr(b, scope)?;
                    if a.ty == TyCtxt::INTEGER_TYPE_ID && b.ty == TyCtxt::INTEGER_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Sub, Box::new(a), Box::new(b)),
                            TyCtxt::INTEGER_TYPE_ID,
                        )
                    } else if a.ty == TyCtxt::DOUBLE_TYPE_ID && b.ty == TyCtxt::DOUBLE_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Sub, Box::new(a), Box::new(b)),
                            TyCtxt::DOUBLE_TYPE_ID,
                        )
                    } else if a.ty != b.ty {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::BinOpTypeMismatch {
                                lhs: a.ty,
                                rhs: b.ty,
                            },
                            message: format!(
                                "binary operation LHS expression has type `{:?}` but RHS expression has `{:?}`",
                                self.tcx.get_type(a.ty),
                                self.tcx.get_type(b.ty)
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    } else {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::UnsupportedType {
                                supported: vec![],
                                found: a.ty,
                            },
                            message: format!(
                                "binary operation has unsupported type `{:?}`",
                                self.tcx.get_type(a.ty),
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    }
                }
                BinOp::Mul => {
                    let a = self.lower_expr(a, scope)?;
                    let b = self.lower_expr(b, scope)?;
                    if a.ty == TyCtxt::INTEGER_TYPE_ID && b.ty == TyCtxt::INTEGER_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Mul, Box::new(a), Box::new(b)),
                            TyCtxt::INTEGER_TYPE_ID,
                        )
                    } else if a.ty == TyCtxt::DOUBLE_TYPE_ID && b.ty == TyCtxt::DOUBLE_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Mul, Box::new(a), Box::new(b)),
                            TyCtxt::DOUBLE_TYPE_ID,
                        )
                    } else if a.ty != b.ty {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::BinOpTypeMismatch {
                                lhs: a.ty,
                                rhs: b.ty,
                            },
                            message: format!(
                                "binary operation LHS expression has type `{:?}` but RHS expression has `{:?}`",
                                self.tcx.get_type(a.ty),
                                self.tcx.get_type(b.ty)
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    } else {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::UnsupportedType {
                                supported: vec![],
                                found: a.ty,
                            },
                            message: format!(
                                "binary operation has unsupported type `{:?}`",
                                self.tcx.get_type(a.ty),
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    }
                }
                BinOp::Div => {
                    let a = self.lower_expr(a, scope)?;
                    let b = self.lower_expr(b, scope)?;
                    if a.ty == TyCtxt::INTEGER_TYPE_ID && b.ty == TyCtxt::INTEGER_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Div, Box::new(a), Box::new(b)),
                            TyCtxt::INTEGER_TYPE_ID,
                        )
                    } else if a.ty == TyCtxt::DOUBLE_TYPE_ID && b.ty == TyCtxt::DOUBLE_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Div, Box::new(a), Box::new(b)),
                            TyCtxt::DOUBLE_TYPE_ID,
                        )
                    } else if a.ty != b.ty {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::BinOpTypeMismatch {
                                lhs: a.ty,
                                rhs: b.ty,
                            },
                            message: format!(
                                "binary operation LHS expression has type `{:?}` but RHS expression has `{:?}`",
                                self.tcx.get_type(a.ty),
                                self.tcx.get_type(b.ty)
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    } else {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::UnsupportedType {
                                supported: vec![],
                                found: a.ty,
                            },
                            message: format!(
                                "binary operation has unsupported type `{:?}`",
                                self.tcx.get_type(a.ty),
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    }
                }
                BinOp::Mod => {
                    let a = self.lower_expr(a, scope)?;
                    let b = self.lower_expr(b, scope)?;
                    if a.ty == TyCtxt::INTEGER_TYPE_ID && b.ty == TyCtxt::INTEGER_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Mod, Box::new(a), Box::new(b)),
                            TyCtxt::INTEGER_TYPE_ID,
                        )
                    } else if a.ty == TyCtxt::DOUBLE_TYPE_ID && b.ty == TyCtxt::DOUBLE_TYPE_ID {
                        (
                            hir::ExprKind::Binary(hir::BinOp::Mod, Box::new(a), Box::new(b)),
                            TyCtxt::DOUBLE_TYPE_ID,
                        )
                    } else if a.ty != b.ty {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::BinOpTypeMismatch {
                                lhs: a.ty,
                                rhs: b.ty,
                            },
                            message: format!(
                                "binary operation LHS expression has type `{:?}` but RHS expression has `{:?}`",
                                self.tcx.get_type(a.ty),
                                self.tcx.get_type(b.ty)
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    } else {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::UnsupportedType {
                                supported: vec![],
                                found: a.ty,
                            },
                            message: format!(
                                "binary operation has unsupported type `{:?}`",
                                self.tcx.get_type(a.ty),
                            ),
                            span: expr.span,
                        });
                        return Err(());
                    }
                }
            },
        };

        Ok(hir::Expr {
            kind,
            span: expr.span,
            ty,
        })
    }

    fn lower_non_call_or_index_ident(
        &mut self,
        ident: Ident,
        scope: &mut LexicalScope<'_>,
    ) -> Result<DeclId, ()> {
        if let Some(decl_id) = scope.lookup(ident.name) {
            let decl = self.tcx.get_decl(decl_id);
            let ty = self.tcx.get_type(decl.ty);
            match ty {
                Type::Procedure { .. } => {
                    self.sess.emit_diagnostic(Diagnostic {
                        kind: DiagnosticKind::UsingProcedureNameAsValue,
                        message: format!(
                            "cannot use procedure name `{}` as value",
                            self.tcx.interner.resolve(ident.name).unwrap()
                        ),
                        span: ident.span,
                    });
                    Err(())
                }
                Type::Array { .. } => {
                    self.sess.emit_diagnostic(Diagnostic {
                        kind: DiagnosticKind::UsingArrayNameAsValue,
                        message: format!(
                            "cannot use array name `{}` as value",
                            self.tcx.interner.resolve(ident.name).unwrap()
                        ),
                        span: ident.span,
                    });
                    Err(())
                }
                Type::Integer | Type::Double | Type::Bool | Type::Unit => Ok(decl_id),
            }
        } else {
            self.sess.emit_diagnostic(Diagnostic {
                kind: DiagnosticKind::UndeclaredName,
                message: format!(
                    "use of undefined name `{}`",
                    self.tcx.interner.resolve(ident.name).unwrap()
                ),
                span: ident.span,
            });
            Err(())
        }
    }

    fn lower_call_or_index_ident(
        &mut self,
        ident: Ident,
        scope: &mut LexicalScope<'_>,
    ) -> Result<DeclId, ()> {
        trace!(
            "lower_call_or_index_ident: ident.name = {:?}, resolved = {}",
            ident.name,
            self.tcx.interner.resolve(ident.name).unwrap()
        );
        trace!("lower_call_or_index_ident: scope:\n{:#?}", scope);
        if let Some(decl_id) = scope.lookup(ident.name) {
            let decl = self.tcx.get_decl(decl_id);
            let ty = self.tcx.get_type(decl.ty);
            match ty {
                Type::Array { .. } | Type::Procedure { .. } => Ok(decl_id),
                Type::Integer | Type::Double | Type::Bool | Type::Unit => {
                    self.sess.emit_diagnostic(Diagnostic {
                        kind: DiagnosticKind::CallOrIndexIntoPrimitiveType,
                        message: format!(
                            "cannot call or index into variable of primitive type `{}`",
                            self.tcx.interner.resolve(ident.name).unwrap()
                        ),
                        span: ident.span,
                    });
                    Err(())
                }
            }
        } else {
            self.sess.emit_diagnostic(Diagnostic {
                kind: DiagnosticKind::UndeclaredName,
                message: format!(
                    "use of undefined name `{}`",
                    self.tcx.interner.resolve(ident.name).unwrap()
                ),
                span: ident.span,
            });
            Err(())
        }
    }

    fn lower_args(
        &mut self,
        args: &[Expr],
        scope: &mut LexicalScope<'_>,
    ) -> Result<Vec<hir::Expr>, ()> {
        let mut hir_args = Vec::new();
        for arg in args {
            hir_args.push(self.lower_expr(arg, scope)?);
        }
        Ok(hir_args)
    }

    fn process_non_param_decls(
        &mut self,
        decls: &[ast::Decl],
        params: &[Ident],
        scope: &mut LexicalScope<'_>,
    ) -> Result<Vec<DeclId>, ()> {
        let mut decl_ids = Vec::new();
        let param_names = params.iter().map(|p| p.name).collect::<Vec<_>>();

        // First pass: register the non-param decls with primitive types.
        for decl in decls {
            if !param_names.contains(&decl.ident.name) {
                match &decl.ty {
                    Ty::Scalar(..) => {
                        let ty = self.lower_ty_to_ty(&decl.ty, scope)?;
                        let decl_id = self.tcx.alloc_decl(Decl {
                            name: decl.ident.name,
                            ty,
                        });
                        scope.try_define(decl.ident.name, decl_id)?;
                        decl_ids.push(decl_id);
                    }
                    Ty::Array { .. } => {}
                }
            }
        }

        // Second pass: resolve the non-param decls with non-primitive types
        for decl in decls {
            if !param_names.contains(&decl.ident.name) {
                match &decl.ty {
                    Ty::Array { .. } => {
                        let ty = self.lower_ty_to_ty(&decl.ty, scope)?;
                        let decl_id = self.tcx.alloc_decl(Decl {
                            name: decl.ident.name,
                            ty,
                        });
                        scope.try_define(decl.ident.name, decl_id)?;
                        decl_ids.push(decl_id);
                    }
                    Ty::Scalar(..) => {}
                }
            }
        }

        Ok(decl_ids)
    }

    fn lower_stmts(
        &mut self,
        stmts: &[Stmt],
        scope: &mut LexicalScope<'_>,
    ) -> Result<Vec<hir::Stmt>, ()> {
        let mut hir_stmts = Vec::new();
        for stmt in stmts {
            hir_stmts.push(self.lower_stmt(stmt, scope)?);
        }
        Ok(hir_stmts)
    }

    fn lower_stmt(&mut self, stmt: &Stmt, scope: &mut LexicalScope<'_>) -> Result<hir::Stmt, ()> {
        let kind = match &stmt.kind {
            StmtKind::DoLoop(do_loop) => hir::StmtKind::DoLoop(self.lower_do_loop(do_loop, scope)?),
            StmtKind::Assign(assign) => hir::StmtKind::Assign(self.lower_assign(assign, scope)?),
            StmtKind::If(if_stmt) => hir::StmtKind::If(self.lower_if_stmt(if_stmt, scope)?),
        };

        Ok(hir::Stmt {
            kind,
            span: stmt.span,
        })
    }

    fn lower_do_loop(
        &mut self,
        do_loop: &DoLoop,
        scope: &mut LexicalScope<'_>,
    ) -> Result<hir::DoLoop, ()> {
        let lower_bound = self.lower_expr(&do_loop.lower_bound, scope)?;
        let upper_bound = self.lower_expr(&do_loop.upper_bound, scope)?;
        let step = do_loop
            .step
            .as_ref()
            .map(|s| self.lower_expr(&s, scope))
            .transpose()?;
        let mut loop_scope = LexicalScope {
            kind: LexicalScopeKind::Regular,
            names: Default::default(),
            parent: Some(scope),
        };
        let stmts = self.lower_stmts(&do_loop.stmts, &mut loop_scope)?;

        Ok(hir::DoLoop {
            lower_bound,
            upper_bound,
            step,
            stmts,
            span: do_loop.span,
        })
    }

    fn lower_assign(
        &mut self,
        assign: &Assign,
        scope: &mut LexicalScope<'_>,
    ) -> Result<hir::Assign, ()> {
        let lhs = self.lower_lvalue_expr(&assign.lhs, scope)?;
        let rhs = self.lower_expr(&assign.rhs, scope)?;

        Ok(hir::Assign {
            lhs,
            rhs,
            span: assign.span,
        })
    }

    fn lower_lvalue_expr(
        &mut self,
        lvalue_expr: &Expr,
        scope: &mut LexicalScope<'_>,
    ) -> Result<hir::Expr, ()> {
        let (kind, ty) = match &lvalue_expr.kind {
            ExprKind::IntConst(..)
            | ExprKind::DoubleConst(..)
            | ExprKind::Unary(..)
            | ExprKind::Binary(..) => {
                self.sess.emit_diagnostic(Diagnostic {
                    kind: DiagnosticKind::NotAssignable,
                    message: "expression cannot be assigned to".to_owned(),
                    span: lvalue_expr.span,
                });
                return Err(());
            }
            ExprKind::Fetch(ident) => {
                let decl_id = self.lower_ident(*ident, scope)?;
                let decl = self.tcx.get_decl(decl_id);
                (hir::ExprKind::Fetch(decl_id), decl.ty)
            }
            ExprKind::CallOrIndex { target, args } => {
                let args = self.lower_args(args, scope)?;
                let target_decl_id = self.lower_call_or_index_ident(*target, scope)?;
                let target_decl = self.tcx.get_decl(target_decl_id);
                let target_ty = self.tcx.get_type(target_decl.ty);

                match &target_ty {
                    Type::Procedure { .. } => {
                        self.sess.emit_diagnostic(Diagnostic {
                            kind: DiagnosticKind::NotAssignable,
                            message: "cannot assign to call expression".to_owned(),
                            span: lvalue_expr.span,
                        });
                        return Err(());
                    }
                    Type::Array {
                        base_ty,
                        dimensions,
                    } => {
                        if *dimensions != args.len() {
                            self.sess.emit_diagnostic(Diagnostic {
                                kind: DiagnosticKind::ArrayIndexDimensionMismatch {
                                    expected: *dimensions,
                                    found: args.len(),
                                },
                                message: format!(
                                    "array index dimension mismatch: expected `{}` but found `{}`",
                                    *dimensions,
                                    args.len()
                                ),
                                span: lvalue_expr.span,
                            });
                            return Err(());
                        }

                        for arg in &args {
                            if arg.ty != TyCtxt::INTEGER_TYPE_ID {
                                self.sess.emit_diagnostic(Diagnostic {
                                    kind: DiagnosticKind::NonIntegerIndexExpr,
                                    message: "index expressions must be of integer type".to_owned(),
                                    span: arg.span,
                                });
                                return Err(());
                            }
                        }

                        (
                            hir::ExprKind::Index {
                                target: target_decl_id,
                                args,
                            },
                            *base_ty,
                        )
                    }
                    _ => unreachable!(),
                }
            }
        };

        Ok(hir::Expr {
            kind,
            span: lvalue_expr.span,
            ty,
        })
    }

    fn lower_ident(&mut self, ident: Ident, scope: &mut LexicalScope<'_>) -> Result<DeclId, ()> {
        scope.lookup(ident.name).ok_or_else(|| {
            self.sess.emit_diagnostic(Diagnostic {
                kind: DiagnosticKind::UndeclaredName,
                message: format!(
                    "cannot find `{}` in current scope",
                    self.tcx.interner.resolve(ident.name).unwrap()
                ),
                span: ident.span,
            });
        })
    }

    fn lower_if_stmt(
        &mut self,
        if_stmt: &IfStmt,
        scope: &mut LexicalScope<'_>,
    ) -> Result<hir::IfStmt, ()> {
        let cond = self.lower_expr(&if_stmt.cond, scope)?;
        if cond.ty != TyCtxt::BOOL_TYPE_ID {
            self.sess.emit_diagnostic(Diagnostic {
                kind: DiagnosticKind::UnexpectedType {
                    expected: TyCtxt::BOOL_TYPE_ID,
                    found: cond.ty,
                },
                message: format!(
                    "expected `{:?}` type, found `{:?}` type",
                    self.tcx.get_type(TyCtxt::BOOL_TYPE_ID),
                    self.tcx.get_type(cond.ty)
                ),
                span: cond.span,
            });
            return Err(());
        }

        let mut if_stmt_scope = LexicalScope {
            kind: LexicalScopeKind::Regular,
            names: Default::default(),
            parent: Some(scope),
        };
        let if_stmts = self.lower_stmts(&if_stmt.if_stmts, &mut if_stmt_scope)?;

        let elsif_stmts = self.lower_elsif_stmts(&if_stmt.elsif_stmts, scope)?;

        let mut else_stmt_scope = LexicalScope {
            kind: LexicalScopeKind::Regular,
            names: Default::default(),
            parent: Some(scope),
        };
        let else_stmts = self.lower_stmts(&if_stmt.else_stmts, &mut else_stmt_scope)?;

        Ok(hir::IfStmt {
            cond,
            if_stmts,
            elsif_stmts,
            else_stmts,
            span: if_stmt.span,
        })
    }

    fn lower_elsif_stmts(
        &mut self,
        elsif_stmts: &[ElsifStmt],
        scope: &mut LexicalScope<'_>,
    ) -> Result<Vec<hir::ElsifStmt>, ()> {
        let mut hir_elsif_stmts = Vec::new();

        for elsif_stmt in elsif_stmts {
            hir_elsif_stmts.push(self.lower_elsif_stmt(elsif_stmt, scope)?);
        }

        Ok(hir_elsif_stmts)
    }

    fn lower_elsif_stmt(
        &mut self,
        elsif_stmt: &ElsifStmt,
        scope: &mut LexicalScope<'_>,
    ) -> Result<hir::ElsifStmt, ()> {
        let cond = self.lower_expr(&elsif_stmt.cond, scope)?;

        let mut stmts_scope = LexicalScope {
            kind: LexicalScopeKind::Regular,
            names: Default::default(),
            parent: Some(scope),
        };

        let stmts = self.lower_stmts(&elsif_stmt.stmts, &mut stmts_scope)?;

        Ok(hir::ElsifStmt {
            cond,
            stmts,
            span: elsif_stmt.span,
        })
    }
}
