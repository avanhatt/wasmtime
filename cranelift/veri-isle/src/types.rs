//! Types for translation to SMT.
//!

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SMTType {
    // logic QF_BV https://smtlib.cs.uiowa.edu/version1/logics/QF_BV.smt
    BitVector(usize),
}

impl SMTType {
    pub fn width(&self) -> i8 {
        match self {
            &Self::BitVector(s) => s as i8,
        }
    }
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
