//! External definitions need to specify both their assumptions and what they
//! produce.
//!
//! Right now, this uses the rsmt2 crate's datatypes.

use crate::types::SMTType;
use rsmt2::Solver;

impl SMTType {
    pub fn to_rsmt2_str(self) -> String {
        match self {
            SMTType::BitVector(width) => format!("(_ BitVec {})", width),
        }
    }
}

// let mut solver = Solver::default_z3(()).unwrap()

fn add_external_semantics(solver: &mut Solver<()>, name: &str, ty: SMTType) {
    let arg_ty = ty.to_rsmt2_str();
    match name {
        "fits_in_64" => {
            // Return the type, identity fn
            solver
                .define_fun("fits_in_64", &[("t", arg_ty.clone())], arg_ty, "t")
                .unwrap();
        }
        "iadd" => {
            // Return the type, identity fn
            solver
                .define_fun(
                    "iadd",
                    &[("x", arg_ty.clone()), ("y", arg_ty.clone())],
                    arg_ty,
                    "(bvadd x y)",
                )
                .unwrap();
        }
        _ => unimplemented!(),
    }
}
