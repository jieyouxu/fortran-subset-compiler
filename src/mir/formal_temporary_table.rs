use std::collections::BTreeMap;

use ordered_float::OrderedFloat;

use super::{Opcode, TemporaryId};

/// The formal temporary table stores records of opcode and inputs for each instruction alongside
/// the temporary for the result.
#[derive(Debug, PartialEq)]
pub struct FormalTemporaryTable {
    records: BTreeMap<(Opcode, Vec<TempOrConst>), TemporaryId>,
}

#[derive(Debug, Copy, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub enum TempOrConst {
    Temp(TemporaryId),
    IntConst(i64),
    DoubleConst(OrderedFloat<f64>),
}

impl FormalTemporaryTable {
    pub fn new() -> Self {
        Self {
            records: Default::default(),
        }
    }

    pub fn lookup(&self, key: &(Opcode, Vec<TempOrConst>)) -> Option<TemporaryId> {
        self.records.get(key).copied()
    }

    pub fn insert(&mut self, key: (Opcode, Vec<TempOrConst>), temp: TemporaryId) {
        self.insert(key, temp)
    }
}
