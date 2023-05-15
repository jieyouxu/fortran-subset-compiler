use std::collections::BTreeMap;

use super::{Opcode, TemporaryId};

/// The formal temporary table stores records of opcode and inputs for each instruction alongside
/// the temporary for the result.
#[derive(Debug, PartialEq)]
pub struct FormalTemporaryTable {
    records: BTreeMap<(Opcode, Vec<TemporaryId>), TemporaryId>,
}

impl FormalTemporaryTable {
    pub fn new() -> Self {
        Self {
            records: Default::default(),
        }
    }

    pub fn lookup(&self, key: &(Opcode, Vec<TemporaryId>)) -> Option<TemporaryId> {
        self.records.get(key).copied()
    }

    pub fn insert(&mut self, key: (Opcode, Vec<TemporaryId>), temp: TemporaryId) {
        self.insert(key, temp)
    }
}
