use super::{BasicBlockId, TemporaryId};

/// Subset of instructions used in the Building an Optimizing Compiler examples.
#[derive(Debug, PartialEq)]
pub enum Instruction {
    /// Load constant `c` into temporary `dst`.
    ILDC { c: Const, dst: TemporaryId },
    /// Copy integer temporary `src` into `dst`.
    I2I { src: TemporaryId, dst: TemporaryId },
    /// Load integer from memory location `src` into `dst`.
    ISLD { src: TemporaryId, dst: TemporaryId },
    /// Place true in `dst` iff `t1 > t2`.
    ICMPGT {
        t1: TemporaryId,
        t2: TemporaryId,
        dst: TemporaryId,
    },
    /// If `cond` is true, branch to `true_block`, otherwise branch to `false_block`.
    IBCOND {
        cond: TemporaryId,
        true_block: BasicBlockId,
        false_block: BasicBlockId,
    },
    /// Integer `dst` = `t1` - `t2`.
    ISUB {
        t1: TemporaryId,
        t2: TemporaryId,
        dst: TemporaryId,
    },
    /// Integer `dst` = `t1` * `t2`.
    IMUL {
        t1: TemporaryId,
        t2: TemporaryId,
        dst: TemporaryId,
    },
    /// Integer `dst` = `t1` + `t2`.
    IADD {
        t1: TemporaryId,
        t2: TemporaryId,
        dst: TemporaryId,
    },
    /// Store value `src` into integer location `dst`.
    ISST { src: TemporaryId, dst: TemporaryId },
    /// Load double in address `src` into temporary `dst`.
    DSLD { src: TemporaryId, dst: TemporaryId },
    /// Store value in double temporary `src` into address `dst`.
    DSST { src: TemporaryId, dst: TemporaryId },
    /// Place absolute value of `src` into `dst`.
    DABS { src: TemporaryId, dst: TemporaryId },
    /// Place true in `dst` iff `sf1 <= sf2`.
    DCMPLE {
        sf1: TemporaryId,
        sf2: TemporaryId,
        dst: TemporaryId,
    },
    /// If `cond` is true, branch to `true_block`, otherwise branch to `false_block`.
    DBCOND {
        cond: TemporaryId,
        true_block: BasicBlockId,
        false_block: BasicBlockId,
    },
    /// Copy value from `src` into `dst.
    D2D { src: TemporaryId, dst: TemporaryId },
    /// Unconditionally branch to `target_block`.
    BR { target_block: BasicBlockId },
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Opcode {
    ILDC,
    I2I,
    ISLD,
    ICMPGT,
    IBCOND,
    ISUB,
    IMUL,
    IADD,
    ISST,
    DSLD,
    DSST,
    DABS,
    DCMPLE,
    DBCOND,
    D2D,
    BR,
}

#[derive(Debug, PartialEq)]
pub enum Const {
    Integer(i64),
    Double(f64),
}

impl Instruction {
    pub fn opcode(&self) -> Opcode {
        match self {
            Instruction::ILDC { .. } => Opcode::ILDC,
            Instruction::I2I { .. } => Opcode::I2I,
            Instruction::ISLD { .. } => Opcode::ISLD,
            Instruction::ICMPGT { .. } => Opcode::ICMPGT,
            Instruction::IBCOND { .. } => Opcode::IBCOND,
            Instruction::ISUB { .. } => Opcode::ISUB,
            Instruction::IMUL { .. } => Opcode::IMUL,
            Instruction::IADD { .. } => Opcode::IADD,
            Instruction::ISST { .. } => Opcode::ISST,
            Instruction::DSLD { .. } => Opcode::DSLD,
            Instruction::DSST { .. } => Opcode::DSST,
            Instruction::DABS { .. } => Opcode::DABS,
            Instruction::DCMPLE { .. } => Opcode::DCMPLE,
            Instruction::DBCOND { .. } => Opcode::DBCOND,
            Instruction::D2D { .. } => Opcode::D2D,
            Instruction::BR { .. } => Opcode::BR,
        }
    }

    pub fn targets(&self) -> impl Iterator<Item = TemporaryId> {
        match self {
            Instruction::ILDC { dst, .. } => vec![*dst].into_iter(),
            Instruction::I2I { dst, .. } => vec![*dst].into_iter(),
            Instruction::ISLD { dst, .. } => vec![*dst].into_iter(),
            Instruction::ICMPGT { dst, .. } => vec![*dst].into_iter(),
            Instruction::IBCOND { .. } => vec![].into_iter(),
            Instruction::ISUB { dst, .. } => vec![*dst].into_iter(),
            Instruction::IMUL { dst, .. } => vec![*dst].into_iter(),
            Instruction::IADD { dst, .. } => vec![*dst].into_iter(),
            Instruction::ISST { dst, .. } => vec![*dst].into_iter(),
            Instruction::DSLD { dst, .. } => vec![*dst].into_iter(),
            Instruction::DSST { dst, .. } => vec![*dst].into_iter(),
            Instruction::DABS { dst, .. } => vec![*dst].into_iter(),
            Instruction::DCMPLE { dst, .. } => vec![*dst].into_iter(),
            Instruction::DBCOND { .. } => vec![].into_iter(),
            Instruction::D2D { dst, .. } => vec![*dst].into_iter(),
            Instruction::BR { .. } => vec![].into_iter(),
        }
    }
}
