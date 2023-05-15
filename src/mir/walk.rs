use super::instructions::Opcode;
use super::{BasicBlockId, FlowGraphBuilder, TemporaryId};
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
    pub fn novalue_walk_program(&mut self, program: &Program) {
        todo!()
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
