//! Internal IR for relevant SMT types. Currently just booleans and bitvectors.
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
    // Nodes
    Const(SMTType, i128),
    Var(SMTType, String),

    // Unary operators
    BVNeg(SMTType, Box<BVExpr>),
    BVNot(SMTType, Box<BVExpr>),

    // Binary operators
    BVAdd(SMTType, Box<BVExpr>, Box<BVExpr>),
    BVSub(SMTType, Box<BVExpr>, Box<BVExpr>),
    BVAnd(SMTType, Box<BVExpr>, Box<BVExpr>),

    // Conversions
    BVZeroExt(SMTType, usize, Box<BVExpr>),
    BVSignExt(SMTType, usize, Box<BVExpr>),
    BVExtract(SMTType, usize, usize, Box<BVExpr>),
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
            BVExpr::BVZeroExt(t, _, _) => t,
            BVExpr::BVSignExt(t, _, _) => t,
            BVExpr::BVExtract(t, _, _, _) => t,
        }
    }
}

impl SMTType {
    pub fn bool_eq(x: BVExpr, y: BVExpr) -> BoolExpr {
        BoolExpr::Eq(Box::new(x), Box::new(y))
    }

    pub fn width(&self) -> usize {
        match self {
            &Self::BitVector(s) => s,
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
        assert_eq!(self.width(), x.ty().width());
        f(*self, Box::new(x))
    }

    pub fn bv_binary<F: Fn(SMTType, Box<BVExpr>, Box<BVExpr>) -> BVExpr>(
        &self,
        f: F,
        x: BVExpr,
        y: BVExpr,
    ) -> BVExpr {
        assert!(self.is_bv());
        assert_eq!(self.width(), x.ty().width());
        assert_eq!(self.width(), y.ty().width());
        f(*self, Box::new(x), Box::new(y))
    }

    pub fn bv_extend<F: Fn(SMTType, usize, Box<BVExpr>) -> BVExpr>(
        &self,
        f: F,
        i: usize,
        x: BVExpr,
    ) -> BVExpr {
        assert!(self.is_bv());
        assert_eq!(self.width(), x.ty().width());
        assert!(i >= 0);
        let new_width = self.width() + i;
        f(SMTType::BitVector(new_width as usize), i, Box::new(x))
    }

    /// Extract bits from index l to index h
    pub fn bv_extract(&self, l: usize, h: usize, x: BVExpr) -> BVExpr {
        assert!(self.is_bv());
        assert_eq!(self.width(), x.ty().width());
        assert!(h >= l);
        assert!(l >= 0);
        let new_width = h - l + 1;
        BVExpr::BVExtract(SMTType::BitVector(new_width as usize), l, h, Box::new(x))
    }
}

pub fn all_starting_bitvectors() -> Vec<SMTType> {
    vec![
        SMTType::BitVector(1),
        SMTType::BitVector(8),
        SMTType::BitVector(16),
        SMTType::BitVector(32),
        SMTType::BitVector(64),
        SMTType::BitVector(128),
    ]
}
