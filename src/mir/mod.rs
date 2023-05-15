pub mod formal_temporary_table;
pub mod instructions;
pub mod walk;

use std::collections::{BTreeMap, BTreeSet};

use index_vec::IndexVec;

use formal_temporary_table::FormalTemporaryTable;
use instructions::{Instruction, Opcode};
use ordered_float::OrderedFloat;

use crate::types::TyCtxt;

use self::formal_temporary_table::TempOrConst;

index_vec::define_index_type! {
    pub struct BasicBlockId = u32;
    MAX_INDEX = (i32::max_value() - 1) as usize;
    DEFAULT = BasicBlockId::from_raw_unchecked(i32::max_value() as u32);
}

index_vec::define_index_type! {
    pub struct TemporaryId = u32;
    MAX_INDEX = (i32::max_value() - 1) as usize;
    DEFAULT = TemporaryId::from_raw_unchecked(i32::max_value() as u32);
}

#[derive(Debug, PartialEq, Default)]
pub struct BasicBlock {
    pub id: BasicBlockId,
    pub instructions: Vec<Instruction>,
    /// Set of Basic Blocks that can follow this Basic Block during the execution of the flow graph.
    pub successors: BTreeSet<BasicBlockId>,
    /// Set of Basic Blocks that can precede this Basic Block during the execution of the flow
    /// graph.
    pub predecessors: BTreeSet<BasicBlockId>,
    pub metadata: BasicBlockMetadata,
}

/// Local optimization information.
///
/// A variable temporary T is *killed* by an instruction if the instruction modifies the
/// temporary directly. T is *transparent* in B if there is no instruction in B that might kill
/// T.
#[derive(Debug, PartialEq, Default)]
pub struct BasicBlockMetadata {
    /// A variable temporary T is *locally anticipated* in basic block B if there is an instruction
    /// in B that evaluates T and there is no instruction preceding that instruction in B which
    /// might kill T.
    pub anticipated: BTreeSet<TemporaryId>,
    /// A variable temporary T is *locally available* in basic block B if there is an instruction in
    /// B that evaluates T and there is no instruction following that instruction in B which might
    /// kill T.
    pub available: BTreeSet<TemporaryId>,
}

impl BasicBlock {
    pub fn compute_local(&mut self, global_metadata: &mut GlobalMetadata) {
        let mut modifies: BTreeMap<TemporaryId, BTreeSet<TemporaryId>> = BTreeMap::new();

        for instruction in self.instructions.iter() {
            if let Some(single_target) = instruction.targets().next() {
                // A normal instruction.
                if let Some(killed) = global_metadata.killed.get(&self.id)
                    && !killed.contains(&single_target)
                {
                    self.metadata.anticipated.insert(single_target);
                    // FIXME: add B to ANTLOC(T)?
                }
                self.metadata.available.insert(single_target);
            }

            for target in instruction.targets() {
                // Track temporaries changed.
                // The set modifies(T) contains the set of temporaries and memory locations that are
                // killed by an instruction which has T as a target.

                // FIXME: killed = killed UNION modifies(target)
                // FIXME: available = available SETMINUS modifies(target)
            }
        }

        for target in self.metadata.available.iter() {
            // FIXME: add B to AVLOC(T)
        }

        // FIXME: transp(B) = V - killed
    }
}

#[derive(Debug, PartialEq)]
pub struct Temporary {
    pub id: TemporaryId,
    pub kind: TemporaryKind,
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum TemporaryKind {
    Variable,
    Expression,
}

impl Temporary {
    pub fn new(kind: TemporaryKind) -> Self {
        Self {
            id: TemporaryId::default(),
            kind,
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct MirArena {
    basic_blocks: IndexVec<BasicBlockId, BasicBlock>,
    temporaries: IndexVec<TemporaryId, Temporary>,
}

impl MirArena {
    pub fn alloc_basic_block(&mut self, bb: BasicBlock) -> BasicBlockId {
        let id = self.basic_blocks.push(bb);
        self.basic_blocks.get_mut(id).unwrap().id = id;
        id
    }

    pub fn get_basic_block_mut(&mut self, id: BasicBlockId) -> &mut BasicBlock {
        self.basic_blocks.get_mut(id).unwrap()
    }

    pub fn alloc_temporary(&mut self, temp: Temporary) -> TemporaryId {
        let id = self.temporaries.push(temp);
        self.temporaries.get_mut(id).unwrap().id = id;
        id
    }

    pub fn get_temporary_mut(&mut self, id: TemporaryId) -> &mut Temporary {
        self.temporaries.get_mut(id).unwrap()
    }
}

#[derive(Debug, PartialEq)]
pub struct FlowGraphBuilder<'tcx, 'icx, 'a> {
    pub tcx: &'tcx mut TyCtxt<'icx>,
    pub arena: &'a mut MirArena,
    pub basic_blocks: BTreeSet<BasicBlockId>,
    pub temporaries: BTreeSet<TemporaryId>,
    pub formal_temporary_table: FormalTemporaryTable,
    pub current_block: BasicBlockId,
    pub global_metadata: GlobalMetadata,
}

#[derive(Debug, PartialEq, Default)]
pub struct GlobalMetadata {
    pub killed: BTreeMap<BasicBlockId, BTreeSet<TemporaryId>>,
}

impl<'tcx, 'icx, 'a> FlowGraphBuilder<'tcx, 'icx, 'a> {
    pub fn compute_local(&mut self) {
        for bb_id in self.basic_blocks.iter() {
            self.arena
                .get_basic_block_mut(*bb_id)
                .compute_local(&mut self.global_metadata);
        }
    }

    /// Create an empty flow graph. We construct two basic blocks: `Entry` and `Exit`, which are the
    /// start and exit blocks for the flow graph. The `Entry` block is set as the current block such
    /// that initial instructions are added to the block.
    pub fn initialize_graph(tcx: &'tcx mut TyCtxt<'icx>, arena: &'a mut MirArena) -> Self {
        let entry = arena.alloc_basic_block(BasicBlock::default());
        let exit = arena.alloc_basic_block(BasicBlock::default());

        Self {
            tcx,
            arena,
            basic_blocks: BTreeSet::from_iter([entry, exit]),
            temporaries: Default::default(),
            formal_temporary_table: FormalTemporaryTable::new(),
            current_block: entry,
            global_metadata: GlobalMetadata {
                killed: Default::default(),
            },
        }
    }

    /// Create a new empty block.
    pub fn create_block(&mut self) -> BasicBlockId {
        self.arena.alloc_basic_block(BasicBlock::default())
    }

    /// Make the `block` the current block. All future instructions will be added to the end of this
    /// `block`.
    pub fn start_block(&mut self, block: BasicBlockId) {
        self.current_block = block;
    }

    fn new_temporary(&mut self, kind: TemporaryKind) -> TemporaryId {
        self.arena.alloc_temporary(Temporary::new(kind))
    }

    fn insert_instruction(&mut self, ins: Instruction) {
        let current_block = self.arena.get_basic_block_mut(self.current_block);
        current_block.instructions.push(ins);
    }

    pub(crate) fn binary_instruct(
        &mut self,
        opcode: Opcode,
        t1: TemporaryId,
        t2: TemporaryId,
    ) -> TemporaryId {
        let key = (opcode, vec![TempOrConst::Temp(t1), TempOrConst::Temp(t2)]);
        let dst = if let Some(dst) = self.formal_temporary_table.lookup(&key) {
            dst
        } else {
            let new_temp = self.new_temporary(TemporaryKind::Expression);
            self.formal_temporary_table.insert(key, new_temp);
            new_temp
        };

        let ins = match opcode {
            Opcode::ISUB => Instruction::ISUB { t1, t2, dst },
            Opcode::IMUL => Instruction::IMUL { t1, t2, dst },
            Opcode::IADD => Instruction::IADD { t1, t2, dst },
            Opcode::DSUB => Instruction::DSUB { t1, t2, dst },
            Opcode::DMUL => Instruction::DMUL { t1, t2, dst },
            Opcode::DADD => Instruction::DADD { t1, t2, dst },
            _ => unreachable!(),
        };
        self.insert_instruction(ins);

        dst
    }

    pub(crate) fn int_const_instruct(&mut self, c: i64) -> TemporaryId {
        let key = (Opcode::ILDC, vec![TempOrConst::IntConst(c)]);
        let dst = if let Some(dst) = self.formal_temporary_table.lookup(&key) {
            dst
        } else {
            let new_temp = self.new_temporary(TemporaryKind::Expression);
            self.formal_temporary_table.insert(key, new_temp);
            new_temp
        };

        self.insert_instruction(Instruction::ILDC { c, dst });

        dst
    }

    pub(crate) fn double_const_instruct(&mut self, c: f64) -> TemporaryId {
        let key = (
            Opcode::DLDC,
            vec![TempOrConst::DoubleConst(OrderedFloat(c))],
        );
        let dst = if let Some(dst) = self.formal_temporary_table.lookup(&key) {
            dst
        } else {
            let new_temp = self.new_temporary(TemporaryKind::Expression);
            self.formal_temporary_table.insert(key, new_temp);
            new_temp
        };

        self.insert_instruction(Instruction::DLDC { c, dst });

        dst
    }
}
