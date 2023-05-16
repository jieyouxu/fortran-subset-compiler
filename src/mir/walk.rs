use super::instructions::Opcode;
use super::{BasicBlockId, FlowGraphBuilder, TemporaryId};
use crate::span::Span;
use crate::types::hir::*;
use crate::types::*;

impl<'tcx, 'icx, 'a> FlowGraphBuilder<'tcx, 'icx, 'a> {
    /// Value context: when operand is expression, we walk expression and create a temporary
    /// which contains the value, and insert instructions in the flow graph.
    pub fn value_walk(&mut self, expr: &Expr) -> TemporaryId {
        match &expr.kind {
            ExprKind::IntConst(c) => self.int_const_instruct(*c),
            ExprKind::DoubleConst(c) => self.double_const_instruct(*c),
            ExprKind::Fetch(_) => todo!(),
            ExprKind::Call { .. } => todo!(),
            ExprKind::Index { .. } => todo!(),
            ExprKind::Unary(_, _) => todo!(),
            ExprKind::Binary(bin_op, a, b) => {
                let t1 = self.value_walk(a);
                let t2 = self.value_walk(b);

                match bin_op {
                    BinOp::Add => match self.tcx.get_type(expr.ty) {
                        Type::Integer => self.binary_instruct(Opcode::ILDC, t1, t2),
                        Type::Double => self.binary_instruct(Opcode::DLDC, t1, t2),
                        Type::Bool => unimplemented!(),
                        _ => unreachable!(),
                    },
                    BinOp::Sub => match self.tcx.get_type(expr.ty) {
                        Type::Integer => self.binary_instruct(Opcode::ISUB, t1, t2),
                        Type::Double => self.binary_instruct(Opcode::DSUB, t1, t2),
                        Type::Bool => unimplemented!(),
                        _ => unreachable!(),
                    },
                    BinOp::Mul => match self.tcx.get_type(expr.ty) {
                        Type::Integer => self.binary_instruct(Opcode::IMUL, t1, t2),
                        Type::Double => self.binary_instruct(Opcode::DMUL, t1, t2),
                        Type::Bool => unimplemented!(),
                        _ => unreachable!(),
                    },
                    _ => unimplemented!(),
                }
            }
        }
    }

    /// No value context: when subtree is a statement or expression used as statement, we walk the
    /// subtree creating instructions to represent the effect of the subtree without creating a
    /// temporary to hold any final value.
    pub fn novalue_walk_stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            // For a do loop that has the form:
            //
            // DO VAR = START, END, STEP
            //     STMTS
            // END DO
            //
            // We lower into IR as if it was
            //
            // VAR = START
            // WHILE VAR OP END
            //     STMTS
            //     VAR += STEP
            // END WHILE
            StmtKind::DoLoop(do_loop) => {
                let var_expr = Expr {
                    kind: ExprKind::Fetch(do_loop.var),
                    span: do_loop.span,
                    ty: self.tcx.get_decl(do_loop.var).ty,
                };

                let initial_assign = Stmt {
                    kind: StmtKind::Assign(Assign {
                        lhs: var_expr.clone(),
                        rhs: do_loop.start.clone(),
                        span: do_loop.start.span,
                    }),
                    span: Span::dummy(),
                };

                self.novalue_walk_stmt(&initial_assign);

                let cond_expr = Expr {
                    kind: match do_loop.step {
                        Some(_) => todo!(),
                        None => ExprKind::Binary(
                            BinOp::Leq,
                            Box::new(var_expr.clone()),
                            Box::new(do_loop.end.clone()),
                        ),
                    },
                    span: Span::dummy(),
                    ty: self.tcx.bool_type(),
                };

                let after = self.create_block();
                let body = self.create_block();

                self.break_stack.push(after);

                self.flow_walk(&cond_expr, body, after);

                self.start_block(body);

                let update_step_stmt = Stmt {
                    kind: StmtKind::Assign(Assign {
                        lhs: var_expr.clone(),
                        rhs: Expr {
                            kind: ExprKind::Binary(
                                BinOp::Add,
                                Box::new(var_expr),
                                Box::new(do_loop.step.clone().unwrap_or(Expr {
                                    kind: ExprKind::IntConst(1),
                                    span: Span::dummy(),
                                    ty: self.tcx.integer_type(),
                                })),
                            ),
                            span: Span::dummy(),
                            ty: self.tcx.integer_type(),
                        },
                        span: Span::dummy(),
                    }),
                    span: Span::dummy(),
                };

                let mut body_stmts = do_loop.stmts.clone();
                body_stmts.push(update_step_stmt);

                for stmt in body_stmts {
                    self.novalue_walk_stmt(&stmt);
                }

                self.flow_walk(&cond_expr, body, after);

                self.start_block(after);

                self.break_stack.pop();
            }
            StmtKind::Assign(assign) => {
                todo!()
            }
            StmtKind::If(if_stmt) => todo!(),
        }
    }

    /// Flow value context: if subtree represents an expression used to determine branching
    /// operation, we walk the subtree generating the testing and branching instructions
    /// together.
    pub fn flow_walk(&mut self, expr: &Expr, true_block: BasicBlockId, false_block: BasicBlockId) {
        todo!()
    }

    /// Size context: if size of the data represented by subtree is needed, we need to walk it to
    /// generate a temporary holding the value of size of data.
    pub fn size_context(&mut self, expr: &Expr) -> TemporaryId {
        todo!()
    }
}
