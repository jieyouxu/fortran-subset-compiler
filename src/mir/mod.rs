pub mod formal_temporary_table;
pub mod instructions;
pub mod walk;

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};

use index_vec::IndexVec;

use formal_temporary_table::FormalTemporaryTable;
use instructions::{Const, Instruction, Opcode};

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
pub struct FlowGraphBuilder<'a> {
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

impl<'a> FlowGraphBuilder<'a> {
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
    pub fn initialize_graph(arena: &'a mut MirArena) -> Self {
        let entry = arena.alloc_basic_block(BasicBlock::default());
        let exit = arena.alloc_basic_block(BasicBlock::default());

        Self {
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

    pub fn new_temporary(&mut self, kind: TemporaryKind) -> TemporaryId {
        self.arena.alloc_temporary(Temporary::new(kind))
    }

    fn insert_instruction(&mut self, ins: Instruction) {
        let current_block = self.arena.get_basic_block_mut(self.current_block);
        current_block.instructions.push(ins);
    }

    pub fn ildc_instruct(&mut self, c: Const, dst: TemporaryId) {
        self.insert_instruction(Instruction::ILDC { c, dst });
    }

    pub fn i2i_instruct(&mut self, src: TemporaryId, dst: TemporaryId) {
        self.insert_instruction(Instruction::I2I { src, dst });
    }

    pub fn isld_instruct(&mut self, src: TemporaryId, dst: TemporaryId) {
        self.insert_instruction(Instruction::ISLD { src, dst });
    }

    pub fn icmpgt_instruct(&mut self, t1: TemporaryId, t2: TemporaryId, dst: TemporaryId) {
        self.insert_instruction(Instruction::ICMPGT { t1, t2, dst });
    }

    pub fn isub_instruct(&mut self, t1: TemporaryId, t2: TemporaryId, dst: TemporaryId) {
        self.insert_instruction(Instruction::ISUB { t1, t2, dst });
    }

    pub fn imul_instruct(&mut self, t1: TemporaryId, t2: TemporaryId, dst: TemporaryId) {
        self.insert_instruction(Instruction::ISUB { t1, t2, dst });
    }

    pub fn iadd_instruct(&mut self, t1: TemporaryId, t2: TemporaryId, dst: TemporaryId) {
        self.insert_instruction(Instruction::ISUB { t1, t2, dst });
    }

    pub fn isst_instruct(&mut self, src: TemporaryId, dst: TemporaryId) {
        self.insert_instruction(Instruction::ISST { src, dst });
    }

    pub fn dsld_instruct(&mut self, src: TemporaryId, dst: TemporaryId) {
        self.insert_instruction(Instruction::DSLD { src, dst });
    }

    pub fn dsst_instruct(&mut self, src: TemporaryId, dst: TemporaryId) {
        self.insert_instruction(Instruction::DSST { src, dst });
    }

    pub fn dabs_instruct(&mut self, src: TemporaryId, dst: TemporaryId) {
        self.insert_instruction(Instruction::DABS { src, dst });
    }

    pub fn dcmple_instruct(&mut self, sf1: TemporaryId, sf2: TemporaryId, dst: TemporaryId) {
        self.insert_instruction(Instruction::DCMPLE { sf1, sf2, dst });
    }

    pub fn d2d_instruct(&mut self, src: TemporaryId, dst: TemporaryId) {
        self.insert_instruction(Instruction::D2D { src, dst });
    }

    pub fn ibcond_instruct(
        &mut self,
        cond: TemporaryId,
        true_block: BasicBlockId,
        false_block: BasicBlockId,
    ) {
        self.insert_instruction(Instruction::IBCOND {
            cond,
            true_block,
            false_block,
        });
    }

    pub fn dbcond_instruct(
        &mut self,
        cond: TemporaryId,
        true_block: BasicBlockId,
        false_block: BasicBlockId,
    ) {
        self.insert_instruction(Instruction::DBCOND {
            cond,
            true_block,
            false_block,
        });
    }

    pub fn br_instruct(&mut self, target_block: BasicBlockId) {
        self.insert_instruction(Instruction::BR { target_block });
    }
}
