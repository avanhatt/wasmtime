//! Verification Intermediate Representation for relevant SMT types. Currently just booleans and bitvectors.
//!

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VIRAnnotation {
    pub func: FunctionAnnotation,
    pub assertions: Vec<VIRExpr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionAnnotation {
    pub args: Vec<BoundVar>,
    pub result: BoundVar,
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
    IsleType,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VIRExpr {
    // Terminal nodes
    Var(BoundVar),
    Const(VIRType, i128),
    True,
    False,

    // Boolean operations
    Not(Box<VIRExpr>),
    And(Box<VIRExpr>, Box<VIRExpr>),
    Or(Box<VIRExpr>, Box<VIRExpr>),
    Imp(Box<VIRExpr>, Box<VIRExpr>),
    Eq(Box<VIRExpr>, Box<VIRExpr>),
    Lte(Box<VIRExpr>, Box<VIRExpr>),

    // Bitvector operations
    // Unary operators
    BVNeg(VIRType, Box<VIRExpr>),
    BVNot(VIRType, Box<VIRExpr>),

    // Binary operators
    BVAdd(VIRType, Box<VIRExpr>, Box<VIRExpr>),
    BVSub(VIRType, Box<VIRExpr>, Box<VIRExpr>),
    BVAnd(VIRType, Box<VIRExpr>, Box<VIRExpr>),

    // Conversions
    BVZeroExt(VIRType, usize, Box<VIRExpr>),
    BVSignExt(VIRType, usize, Box<VIRExpr>),
    BVExtract(VIRType, usize, usize, Box<VIRExpr>),
}

impl VIRExpr {
    pub fn ty(&self) -> &VIRType {
        match &self {
            VIRExpr::Var(bv) => &bv.ty,
            VIRExpr::Const(t, _) => t,
            VIRExpr::BVNeg(t, _) => t,
            VIRExpr::BVNot(t, _) => t,
            VIRExpr::BVAdd(t, _, _) => t,
            VIRExpr::BVSub(t, _, _) => t,
            VIRExpr::BVAnd(t, _, _) => t,
            VIRExpr::BVZeroExt(t, _, _) => t,
            VIRExpr::BVSignExt(t, _, _) => t,
            VIRExpr::BVExtract(t, _, _, _) => t,
            VIRExpr::True 
            | VIRExpr::False 
            | VIRExpr::Not(..)
            | VIRExpr::And(..)
            | VIRExpr::Or(..)
            | VIRExpr::Imp(..)
            | VIRExpr::Eq(..)
            | VIRExpr::Lte(..) => &VIRType::Bool,
        }
    }
}

impl VIRType {
    pub fn eq(x: VIRExpr, y: VIRExpr) -> VIRExpr {
        assert_eq!(x.ty(), y.ty(), "(= {:?} {:?})", x, y);
        VIRExpr::Eq(Box::new(x), Box::new(y))
    }

    pub fn lte(x: VIRExpr, y: VIRExpr) -> VIRExpr {
        assert_eq!(x.ty(), y.ty(), "(= {:?}{:?})", x, y);
        VIRExpr::Lte(Box::new(x), Box::new(y))
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

    pub fn is_isle_type(&self) -> bool {
        matches!(*self, Self::IsleType)   
    }

    pub fn bv_const(&self, x: i128) -> VIRExpr {
        assert!(self.is_bv());
        VIRExpr::Const(*self, x)
    }

    pub fn isle_type_const(&self, x: i128) -> VIRExpr {
        assert!(self.is_isle_type());
        VIRExpr::Const(*self, x)
    }

    pub fn bv_var(&self, s: String) -> VIRExpr {
        VIRExpr::Var(BoundVar{name: s, ty: *self})
    }

    pub fn bv_unary<F: Fn(VIRType, Box<VIRExpr>) -> VIRExpr>(&self, f: F, x: VIRExpr) -> VIRExpr {
        assert!(self.is_bv());
        assert_eq!(self.width(), x.ty().width());
        f(*self, Box::new(x))
    }

    pub fn bv_binary<F: Fn(VIRType, Box<VIRExpr>, Box<VIRExpr>) -> VIRExpr>(
        &self,
        f: F,
        x: VIRExpr,
        y: VIRExpr,
    ) -> VIRExpr {
        assert!(self.is_bv());
        assert_eq!(self.width(), x.ty().width(), "({:?}, {:?})", x, y);
        assert_eq!(self.width(), y.ty().width(), "({:?}, {:?})", x, y);
        f(*self, Box::new(x), Box::new(y))
    }

    pub fn bv_extend<F: Fn(VIRType, usize, Box<VIRExpr>) -> VIRExpr>(
        &self,
        f: F,
        i: usize,
        x: VIRExpr,
    ) -> VIRExpr {
        assert!(self.is_bv());
        assert_eq!(self.width(), x.ty().width());
        let new_width = self.width() + i;
        f(VIRType::BitVector(new_width as usize), i, Box::new(x))
    }

    /// Extract bits from index l to index h
    pub fn bv_extract(&self, l: usize, h: usize, x: VIRExpr) -> VIRExpr {
        assert!(self.is_bv());
        assert_eq!(self.width(), x.ty().width());
        assert!(h >= l);
        let new_width = h - l + 1;
        VIRExpr::BVExtract(VIRType::BitVector(new_width as usize), l, h, Box::new(x))
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

impl BoundVar {
    pub fn as_expr(&self)-> VIRExpr {
        VIRExpr::Var(self.clone())
    }
}
