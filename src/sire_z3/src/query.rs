use std::fmt::Write;

use sire::sir::*;

use crate::node::Node;
use crate::seq;

pub fn equality_query(def_a: FuncDef, def_b: FuncDef) -> String {
    let arity_a = def_a.arity();
    let arity_b = def_b.arity();

    let clause = match (arity_a, arity_b) {
        (0, 0) => seq!["=", def_a.func_id, def_b.func_id],
        (_, 0) => {
            let args = args_with_ty(&def_a);
            let apply_a = apply(&def_a);
            seq!["exists", args, seq!["=", apply_a, def_b.func_id]]
        }
        (0, _) => {
            let args = args_with_ty(&def_b);
            let apply_b = apply(&def_b);
            seq!["exists", args, seq!["=", def_a.func_id, apply_b]]
        }
        (a, b) if a == b => {
            let args = args_with_ty(&def_a);
            let apply_a = apply(&def_a);
            let apply_b = apply(&def_b);
            seq!["forall", args, seq!["=", apply_a, apply_b]]
        }
        _ => unreachable!(),
    };

    let mut instances = def_a.body.find_datatype_instances();
    for instance in def_b.body.find_datatype_instances() {
        if !instances.contains(&instance) {
            instances.push(instance);
        }
    }

    let tuple_decl = seq![
        "declare-datatypes",
        seq!["T1", "T2"],
        seq![seq!["Tuple", seq!["tuple", seq!["first", "T1"], seq!["second", "T2"]]]]
    ];
    let unit_decl =
        seq!["declare-datatypes", Node::Seq(Vec::new()), seq![seq!["Unit", seq!["unit"]]]];

    let mut query = vec![tuple_decl, unit_decl];

    for ty in instances {
        query.push(seq!["declare-const", "_", Node::from(ty)]);
    }

    query.push(def_a.into());
    query.push(def_b.into());
    query.push(seq!["assert", clause]);
    query.push(seq!["check-sat"]);

    let mut buffer = String::new();

    for line in query {
        writeln!(buffer, "{}", line).unwrap();
    }

    buffer
}

fn args_with_ty(func_def: &FuncDef) -> Node {
    let (args, params) = match &func_def.ty {
        Ty::Func(args, params) => (args, params),
        _ => unreachable!(),
    };

    let seq = args
        .into_iter()
        .enumerate()
        .map(|(index, ty)| seq![format!("x_{}", index), ty.clone()])
        .skip(1)
        .chain(params.into_iter().map(|Param(index, ty)| seq![format!("p_{}", index), ty.clone()]))
        .collect::<Vec<Node>>();

    Node::Seq(seq)
}

fn apply(func_def: &FuncDef) -> Node {
    let (args, params) = match &func_def.ty {
        Ty::Func(args, params) => (args, params),
        _ => unreachable!(),
    };

    let mut seq = vec![func_def.func_id.into()];

    for index in (0..args.len()).skip(1) {
        seq.push(format!("x_{}", index).into());
    }

    for Param(index, _) in params {
        seq.push(format!("p_{}", index).into());
    }

    Node::Seq(seq)
}
