#![feature(box_patterns)]

use rustc::ty::{Const, TyCtxt};

use sire::eval::Evaluator;


pub use io::CheckResult;

mod node;
mod query;
mod io;

pub fn equality_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    const_a: &Const<'tcx>,
    const_b: &Const<'tcx>,
) -> CheckResult {
    let mut evaluator = Evaluator::from_tcx(tcx);
    let def_a = evaluator.eval_const(*const_a).unwrap();
    let def_b = evaluator.eval_const(*const_b).unwrap();

    if def_a.func_id == def_b.func_id {
        return CheckResult::Sat;
    }

    let query = query::equality_query(def_a, def_b);

    io::call(&query).unwrap()
}
