use super::{BasicBlockId, FlowGraphBuilder, TemporaryId};
use crate::types::hir::*;

impl<'a> FlowGraphBuilder<'a> {
    /// Value context: when operand is expression, we walk expression and create a temporary
    /// which contains the value, and inserts instructions in the flow graph.
    pub fn value_walk(&mut self, ast: &Program) -> TemporaryId {
        todo!()
    }

    /// No value context: when subtree is a statement or expression used as statement, we walk the
    /// subtree creating instructions to represent the effect of the subtree without creating a
    /// temporary to hold any final value.
    pub fn novalue_walk(&mut self, ast: &Program) {
        todo!()
    }

    /// Flow value context: if subtree represents an expression used to determine branching
    /// operation, we walk the subtree generating the testing and branching instructions
    /// together.
    pub fn flow_walk(
        &mut self,
        ast: &Program,
        true_block: BasicBlockId,
        false_block: BasicBlockId,
    ) {
        todo!()
    }

    /// Size context: if size of the data represented by subtree is needed, we need to walk it to
    /// generate a temporary holding the value of size of data.
    pub fn size_context(&mut self, ast: &Program) -> TemporaryId {
        todo!()
    }
}
