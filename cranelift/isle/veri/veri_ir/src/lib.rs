//! Verification Intermediate Representation for relevant SMT types. Currently just booleans and bitvectors.
//!

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VIRAnnotation {
    func: FunctionAnnotation,
    assertions: Vec<BoolExpr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionAnnotation {
    args: Vec<BoundVar>,
    result: BoundVar,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundVar {
    pub name: String,
    pub ty: VIRType,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum VIRType {
    // logic QF_BV https://smtlib.cs.uiowa.edu/version1/logics/QF_BV.smt
    BitVector(usize),
    Bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoolExpr {
    True,
    False,
    Not(Box<BoolExpr>),
    And(Box<BoolExpr>, Box<BoolExpr>),
    Or(Box<BoolExpr>, Box<BoolExpr>),
    Imp(Box<BoolExpr>, Box<BoolExpr>),
    Eq(Box<BVExpr>, Box<BVExpr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BVExpr {
    // Nodes
    Const(VIRType, i128),
    Var(VIRType, String),

    // Unary operators
    BVNeg(VIRType, Box<BVExpr>),
    BVNot(VIRType, Box<BVExpr>),

    // Binary operators
    BVAdd(VIRType, Box<BVExpr>, Box<BVExpr>),
    BVSub(VIRType, Box<BVExpr>, Box<BVExpr>),
    BVAnd(VIRType, Box<BVExpr>, Box<BVExpr>),

    // Conversions
    BVZeroExt(VIRType, usize, Box<BVExpr>),
    BVSignExt(VIRType, usize, Box<BVExpr>),
    BVExtract(VIRType, usize, usize, Box<BVExpr>),
}

impl BVExpr {
    pub fn ty(&self) -> VIRType {
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

impl VIRType {
    pub fn bool_eq(x: BVExpr, y: BVExpr) -> BoolExpr {
        BoolExpr::Eq(Box::new(x), Box::new(y))
    }

    pub fn width(&self) -> usize {
        match *self {
            Self::BitVector(s) => s,
            _ => unreachable!("Unexpected type: {:?}", self),
        }
    }

    pub fn is_bv(&self) -> bool {
        matches!(*self, Self::BitVector(_))
    }

    pub fn is_bool(&self) -> bool {
        matches!(*self, Self::Bool)   
    }

    pub fn bv_const(&self, x: i128) -> BVExpr {
        assert!(self.is_bv());
        BVExpr::Const(*self, x)
    }

    pub fn bv_var(&self, s: String) -> BVExpr {
        assert!(self.is_bv());
        BVExpr::Var(*self, s)
    }

    pub fn bv_unary<F: Fn(VIRType, Box<BVExpr>) -> BVExpr>(&self, f: F, x: BVExpr) -> BVExpr {
        assert!(self.is_bv());
        assert_eq!(self.width(), x.ty().width());
        f(*self, Box::new(x))
    }

    pub fn bv_binary<F: Fn(VIRType, Box<BVExpr>, Box<BVExpr>) -> BVExpr>(
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

    pub fn bv_extend<F: Fn(VIRType, usize, Box<BVExpr>) -> BVExpr>(
        &self,
        f: F,
        i: usize,
        x: BVExpr,
    ) -> BVExpr {
        assert!(self.is_bv());
        assert_eq!(self.width(), x.ty().width());
        let new_width = self.width() + i;
        f(VIRType::BitVector(new_width as usize), i, Box::new(x))
    }

    /// Extract bits from index l to index h
    pub fn bv_extract(&self, l: usize, h: usize, x: BVExpr) -> BVExpr {
        assert!(self.is_bv());
        assert_eq!(self.width(), x.ty().width());
        assert!(h >= l);
        let new_width = h - l + 1;
        BVExpr::BVExtract(VIRType::BitVector(new_width as usize), l, h, Box::new(x))
    }
}

pub fn all_starting_bitvectors() -> Vec<VIRType> {
    vec![
        VIRType::BitVector(1),
        VIRType::BitVector(8),
        VIRType::BitVector(16),
        VIRType::BitVector(32),
        VIRType::BitVector(64),
        VIRType::BitVector(128),
    ]
}
