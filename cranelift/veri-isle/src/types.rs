//! Types for translation to SMT.
//!

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SMTType {
    // logic QF_BV https://smtlib.cs.uiowa.edu/version1/logics/QF_BV.smt
    BitVector(usize),
}

pub fn all_considered_bitvectors() -> Vec<SMTType> {
    vec![
        SMTType::BitVector(1),
        SMTType::BitVector(8),
        SMTType::BitVector(16),
        SMTType::BitVector(32),
        SMTType::BitVector(64),
        SMTType::BitVector(128),
    ]
}

impl SMTType {
    pub fn to_rsmt2_str(&self) -> String {
        match self {
            SMTType::BitVector(width) => format!("(_ BitVec {})", width),
        }
    }
}
