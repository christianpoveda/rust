use std::fmt;

use sire::sir::*;

pub(crate) enum Node {
    Atom(String),
    Seq(Vec<Node>),
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Atom(name) => write!(f, "{}", name),
            Node::Seq(nodes) => {
                write!(f, "(")?;
                if let Some(node) = nodes.first() {
                    write!(f, "{}", node)?;
                    for node in &nodes[1..] {
                        write!(f, " {}", node)?;
                    }
                }
                write!(f, ")")
            }
        }
    }
}

#[macro_export]
macro_rules! seq {
    ($($x:expr),*) => {{
        let mut seq = Vec::new();
        $( seq.push($x.into()); )*
        Node::Seq(seq)
    }};
}

impl From<&str> for Node {
    fn from(s: &str) -> Self {
        Node::Atom(s.to_owned())
    }
}

impl From<String> for Node {
    fn from(s: String) -> Self {
        Node::Atom(s)
    }
}

impl From<usize> for Node {
    fn from(uint: usize) -> Self {
        Node::Atom(uint.to_string())
    }
}

impl From<Ty> for Node {
    fn from(ty: Ty) -> Self {
        match ty {
            Ty::Int(size) | Ty::Uint(size) => seq!["_", "BitVec", size],
            Ty::Bool => "Bool".into(),
            Ty::Tuple(vec_ty) => {
                let mut seq = vec!["tuple".into()];
                for ty in vec_ty {
                    seq.push(ty.into());
                }
                Node::Seq(seq)
            }
            _ => unreachable!(),
        }
    }
}

impl From<DefId> for Node {
    fn from(DefId{krate, index, ..}: DefId) -> Self {
        format!("func_{}_{}", krate.as_u32(), index.as_u32()).into()
    }
}

impl From<FuncId> for Node {
    fn from(func_id: FuncId) -> Self {
        match func_id {
            FuncId::DefId(def_id) => def_id.into(),
            FuncId::AnonId(uuid) => format!("func_{}", uuid).into(),
        }
    }
}

impl From<Param> for Node {
    fn from(Param(index, _): Param) -> Self {
        format!("p_{}", index).into()
    }
}

impl From<Value> for Node {
    fn from(value: Value) -> Self {
        match value {
            Value::Arg(index, _) => format!("x_{}", index).into(),
            Value::Const(bits, ty) => match ty {
                Ty::Bool => (bits != 0).to_string().into(),
                _ => seq!["_", format!("bv{}", bits), ty.bits().unwrap()],
            },
            Value::ConstParam(param) => param.into(),
            Value::Function(def_id, _) => def_id.into(),
        }
    }
}

impl From<Expr> for Node {
    fn from(expr: Expr) -> Self {
        let ty = expr.ty();

        match expr {
            Expr::Tuple(mut vec_expr) => {
                if let Some(expr) = vec_expr.pop() {
                    let mut node: Node = expr.into();
                    while let Some(expr) = vec_expr.pop() {
                        node = seq!["tuple", expr, node];
                    }
                    node
                } else {
                    "unit".into()
                }
            }

            Expr::Apply(box fun_expr, args_expr) => {
                let mut seq = vec![fun_expr.into()];
                for expr in args_expr {
                    seq.push(expr.into());
                }
                Node::Seq(seq)
            }

            Expr::BinaryOp(bin_op, box expr_1, box expr_2) => {
                let op = match bin_op {
                    BinOp::Eq => "=".to_owned(),
                    BinOp::Ne => "!=".to_owned(),
                    BinOp::Add => "bvadd".to_owned(),
                    BinOp::Sub => "bvsub".to_owned(),
                    BinOp::Mul => "bvmul".to_owned(),
                    _ => {
                        let mut name = match ty {
                            Ty::Int(_) => "bvu",
                            Ty::Uint(_) => "bvs",
                            _ => unreachable!(),
                        }
                        .to_owned();
                        name += match bin_op {
                            BinOp::Div => "div",
                            BinOp::Rem => "rem",
                            BinOp::Lt => "lt",
                            BinOp::Le => "le",
                            BinOp::Ge => "ge",
                            BinOp::Gt => "gt",
                            _ => unreachable!(),
                        };
                        name
                    }
                };
                seq![op, expr_1, expr_2]
            }

            Expr::Switch(box expr, vec_values, mut vec_results) => {
                let mut node: Node = vec_results.pop().unwrap().into();
                for (value, result) in vec_values.into_iter().zip(vec_results).rev() {
                    node = seq!["ite", seq!["=", expr.clone(), value], result, node];
                }
                node
            }

            Expr::Projection(box expr, index) => {
                let proj = match index {
                    0 => "first",
                    1 => "second",
                    // FIXME: Support larger tuples
                    _ => unimplemented!(),
                };
                seq![proj, expr]
            }

            Expr::Value(value) => value.into(),

            Expr::Uninitialized => unreachable!(),
        }
    }
}

impl From<FuncDef> for Node {
    fn from(func_def: FuncDef) -> Self {
        let def = if func_def.is_recursive() { "define-fun-rec" } else { "define-fun" };

        let func_id = func_def.func_id;
        let body = func_def.body;

        let (mut args, params) = match func_def.ty {
            Ty::Func(args, params) => (args, params),
            _ => unreachable!(),
        };

        let ret_ty = args.remove(0);

        let args_with_ty = args
            .into_iter()
            .enumerate()
            .map(|(index, ty)| seq![format!("x_{}", index + 1), ty.clone()])
            .chain(params.into_iter().map(|Param(index, ty)| seq![format!("p_{}", index), ty.clone()]))
            .collect::<Vec<Node>>();

        seq![def, func_id, Node::Seq(args_with_ty), ret_ty, body]
    }
}
