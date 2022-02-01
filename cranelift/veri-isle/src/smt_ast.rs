


pub enum Term {
    BoolExpr(BoolExpr),
    BVExpr(BVExpr)
}

pub enum BoolExpr {
    True,
    False,
    Not(Box<BoolExpr>),
    And(Box<BoolExpr>, Box<BoolExpr>),
    Or(Box<BoolExpr>, Box<BoolExpr>),
    Imp(Box<BoolExpr>, Box<BoolExpr>),
    Eq(Box<BVExpr>, Box<BVExpr>),
}

pub enum BVExpr {
    Const(i128),
    Var(String),
    BVNeg(Box<BVExpr>),
    BVNot(Box<BVExpr>),
    BVAdd(Box<BVExpr>, Box<BVExpr>),
    BVSub(Box<BVExpr>, Box<BVExpr>),
}