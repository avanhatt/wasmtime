//! Types for translation to SMT.
//!

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SMTType {
    // logic QF_BV https://smtlib.cs.uiowa.edu/version1/logics/QF_BV.smt
    BitVector(usize),
    Bool,
}

#[derive(Clone, Debug)]
pub enum Term {
    BoolExpr(BoolExpr),
    BVExpr(BVExpr),
}

#[derive(Clone, Debug)]
pub enum BoolExpr {
    True,
    False,
    Not(Box<BoolExpr>),
    And(Box<BoolExpr>, Box<BoolExpr>),
    Or(Box<BoolExpr>, Box<BoolExpr>),
    Imp(Box<BoolExpr>, Box<BoolExpr>),
    Eq(Box<BVExpr>, Box<BVExpr>),
}

#[derive(Clone, Debug)]
pub enum BVExpr {
    Const(SMTType, i128),
    Var(SMTType, String),
    BVNeg(SMTType, Box<BVExpr>),
    BVNot(SMTType, Box<BVExpr>),
    BVAdd(SMTType, Box<BVExpr>, Box<BVExpr>),
    BVSub(SMTType, Box<BVExpr>, Box<BVExpr>),
    BVAnd(SMTType, Box<BVExpr>, Box<BVExpr>),
}

impl BVExpr {
    pub fn ty(&self) -> SMTType {
        match *self {
            BVExpr::Const(t, _) => t,
            BVExpr::Var(t, _) => t,
            BVExpr::BVNeg(t, _) => t,
            BVExpr::BVNot(t, _) => t,
            BVExpr::BVAdd(t, _, _) => t,
            BVExpr::BVSub(t, _, _) => t,
            BVExpr::BVAnd(t, _, _) => t,
        }
    }
}

impl SMTType {
    pub fn bool_eq(x: BVExpr, y: BVExpr) -> BoolExpr {
        BoolExpr::Eq(Box::new(x), Box::new(y))
    }

    pub fn width(&self) -> i8 {
        match self {
            &Self::BitVector(s) => s as i8,
            _ => unreachable!("Unexpected type: {:?}", self),
        }
    }

    pub fn is_bv(&self) -> bool {
        match self {
            &Self::BitVector(_) => true,
            _ => false,
        }
    }

    pub fn is_bool(&self) -> bool {
        match self {
            &Self::Bool => true,
            _ => false,
        }
    }

    pub fn bv_const(&self, x: i128) -> BVExpr {
        assert!(self.is_bv());
        BVExpr::Const(*self, x)
    }

    pub fn bv_var(&self, s: String) -> BVExpr {
        assert!(self.is_bv());
        BVExpr::Var(*self, s)
    }

    pub fn bv_unary<F: Fn(SMTType, Box<BVExpr>) -> BVExpr>(&self, f: F, x: BVExpr) -> BVExpr {
        assert!(self.is_bv());
        assert!(self.width() == x.ty().width());
        f(*self, Box::new(x))
    }

    pub fn bv_binary<F: Fn(SMTType, Box<BVExpr>, Box<BVExpr>) -> BVExpr>(
        &self,
        f: F,
        x: BVExpr,
        y: BVExpr,
    ) -> BVExpr {
        assert!(self.is_bv());
        assert!(self.width() == x.ty().width());
        assert!(self.width() == y.ty().width());
        f(*self, Box::new(x), Box::new(y))
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
