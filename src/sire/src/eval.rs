use rustc::mir::interpret::{ConstValue, InterpResult};
use rustc::mir::*;
use rustc::ty::{self, layout::Size, Const, ConstKind, TyCtxt};
use rustc::{err_unsup, err_unsup_format};
use rustc_hir::def_id::DefId;

use crate::analysis::find_loop;
use crate::sir::*;

use self::memory::*;
use self::util::*;

mod memory;
mod util;

#[derive(Clone)]
pub struct Evaluator<'tcx> {
    location: Location,
    memory: Memory<'tcx>,
    def_id: Option<DefId>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Evaluator<'tcx> {
    pub fn from_tcx(tcx: TyCtxt<'tcx>) -> Self {
        Evaluator { location: Location::START, memory: Default::default(), def_id: None, tcx }
    }

    pub fn eval_const(&mut self, constant: Const<'tcx>) -> InterpResult<'tcx, FuncDef> {
        match constant.val {
            ConstKind::Unevaluated(def_id, _, _) => self.eval_mir(def_id),
            ConstKind::Value(_) => {
                let ty = Self::transl_non_fn_ty(constant.ty).ok_or_else(|| {
                    err_unsup_format!("Unsupported ty for ConstValue {:?}", constant.ty)
                })?;
                let value = Self::const_kind_to_value(constant.val, ty.clone())?;
                Ok(FuncDef {
                    func_id: uuid::Uuid::new_v4().into(),
                    body: Expr::Value(value),
                    ty: Ty::Func(vec![ty], Vec::new()),
                })
            }
            val => {
                Err(err_unsup_format!("Unsupported: {:?}", val).into())
            }
        }
    }

    fn eval_mir(&mut self, def_id: DefId) -> InterpResult<'tcx, FuncDef> {
        let mir = self.tcx.optimized_mir(def_id);

        if find_loop(mir).is_some() {
            return Err(err_unsup_format!("The function {:?} contains loops", def_id).into());
        }

        let args_ty = mir
            .local_decls
            .iter()
            .take(mir.arg_count + 1)
            .map(|ld| self.transl_ty(&ld.ty))
            .collect::<InterpResult<'_, Vec<Ty>>>()?;

        self.memory.insert(Place::return_place(), Expr::Uninitialized);

        for (i, arg_ty) in args_ty.iter().enumerate().skip(1) {
            self.memory.insert_from_int(i, Expr::Value(Value::Arg(i, arg_ty.clone())));
        }

        let params = ExtractParams::run(self, &mir);

        let locals_len = mir.local_decls.len();
        let (live, dead) = CheckStorage::run(&mir);

        for i in args_ty.len()..locals_len {
            let local = Local::from_usize(i);
            if !live.contains(&local) {
                self.memory.insert_from_int(i, Expr::Uninitialized);
            }
        }

        self.def_id = Some(def_id);

        self.run()?;

        for i in 1usize..args_ty.len() {
            self.memory.remove_from_int(i)?;
        }

        for i in args_ty.len()..locals_len {
            let local = Local::from_usize(i);
            if !dead.contains(&local) {
                self.memory.remove(&local.into())?;
            }
        }

        let mut body = self.memory.remove(&Place::return_place())?;

        body.optimize();

        assert_eq!(args_ty[0], body.ty());

        if self.memory.is_empty() {
            Ok(FuncDef { body, func_id: def_id.into(), ty: Ty::Func(args_ty.clone(), params) })
        } else {
            Err(err_unsup_format!("Memory is not empty after execution").into())
        }
    }

    fn run(&mut self) -> InterpResult<'tcx> {
        while self.step()? {}
        Ok(())
    }

    fn step(&mut self) -> InterpResult<'tcx, bool> {
        let block_data = self
            .tcx
            .optimized_mir(self.def_id.expect("Bug: DefId should be some"))
            .basic_blocks()
            .get(self.location.block)
            .ok_or_else(|| err_unsup_format!("Basic block not found"))?;

        match block_data.statements.get(self.location.statement_index) {
            Some(statement) => self.eval_statement(statement),
            None => self.eval_terminator(block_data.terminator()),
        }
    }

    fn eval_statement(&mut self, statement: &Statement<'tcx>) -> InterpResult<'tcx, bool> {
        match statement.kind {
            StatementKind::Assign(box (ref place, ref rvalue)) => {
                self.eval_rvalue_into_place(rvalue, place)?;
            }
            StatementKind::StorageLive(local) => {
                self.memory.insert(local.into(), Expr::Uninitialized);
            }
            StatementKind::StorageDead(local) => {
                self.memory.remove(&local.into())?;
            }
            ref sk => {
                return Err(err_unsup_format!("StatementKind {:?} is unsupported", sk).into());
            }
        };
        self.location = self.location.successor_within_block();
        Ok(true)
    }

    fn eval_terminator(&mut self, terminator: &Terminator<'tcx>) -> InterpResult<'tcx, bool> {
        match terminator.kind {
            TerminatorKind::Return => {
                self.location = Location::START;
                Ok(false)
            }
            TerminatorKind::Goto { target } => {
                self.location = target.start_location();
                Ok(true)
            }
            TerminatorKind::Call { ref func, ref args, ref destination, .. } => match destination {
                Some((place, block)) => {
                    let func_expr = self.eval_operand(func)?;
                    let mut args_expr = Vec::new();
                    for op in args {
                        args_expr.push(self.eval_operand(op)?);
                    }
                    *self.memory.get_mut(place)? = Expr::Apply(Box::new(func_expr), args_expr);
                    self.location = block.start_location();
                    Ok(true)
                }
                None => Err(err_unsup_format!("Call terminator does not assign").into()),
            },
            TerminatorKind::SwitchInt {
                ref discr, ref switch_ty, ref values, ref targets, ..
            } => {
                let discr_expr = self.eval_operand(&discr)?;
                let mut values_expr = Vec::new();
                let mut targets_expr = Vec::new();

                for (&bytes, &block) in values.iter().zip(targets) {
                    let mut target_expr = self.fork_eval(block)?;

                    let value_expr = Expr::Value(Value::Const(bytes, self.transl_ty(switch_ty)?));

                    target_expr.replace(&discr_expr, &value_expr);

                    values_expr.push(value_expr);
                    targets_expr.push(target_expr);
                }

                self.location = targets.last().unwrap().start_location();
                self.run()?;

                targets_expr.push(self.memory.get(&Place::return_place())?.clone());

                *self.memory.get_mut(&Place::return_place())? =
                    Expr::Switch(Box::new(discr_expr), values_expr, targets_expr);

                self.location = Location::START;
                Ok(false)
            }
            // FIXME: Handle asserts properly
            TerminatorKind::Assert { ref target, .. } => {
                self.location = target.start_location();
                Ok(true)
            }
            ref tk => Err(err_unsup_format!("TerminatorKind {:?} is not supported", tk).into()),
        }
    }

    fn eval_rvalue_into_place(
        &mut self,
        rvalue: &Rvalue<'tcx>,
        place: &Place<'tcx>,
    ) -> InterpResult<'tcx> {
        let value = match rvalue {
            Rvalue::BinaryOp(bin_op, op1, op2) => Expr::BinaryOp(
                *bin_op,
                Box::new(self.eval_operand(op1)?),
                Box::new(self.eval_operand(op2)?),
            ),
            Rvalue::CheckedBinaryOp(bin_op, op1, op2) => Expr::Tuple(vec![
                Expr::BinaryOp(
                    *bin_op,
                    Box::new(self.eval_operand(op1)?),
                    Box::new(self.eval_operand(op2)?),
                ),
                // FIXME: Check the operation
                Expr::Value(Value::Const(0, Ty::Bool)),
            ]),
            Rvalue::Ref(_, BorrowKind::Shared, place) => self.memory.get(place)?.clone(),
            Rvalue::Use(op) => self.eval_operand(op)?,
            ref rv => return Err(err_unsup_format!("Rvalue {:?} unsupported", rv).into()),
        };

        *self.memory.get_mut(place)? = value;

        Ok(())
    }

    fn eval_operand(&self, operand: &Operand<'tcx>) -> InterpResult<'tcx, Expr> {
        Ok(match operand {
            Operand::Move(Place { local, projection })
            | Operand::Copy(Place { local, projection }) => {
                let expr = self.memory.get(&Place::from(*local))?.clone();
                if let [.., ProjectionElem::Field(field, _)] = &***projection {
                    Expr::Projection(Box::new(expr), field.index())
                } else {
                    expr
                }
            }

            Operand::Constant(constant) => {
                let const_ty = &constant.literal.ty;
                let ty = self.transl_ty(const_ty)?;
                Expr::Value(match ty {
                    Ty::Func(_, _) => match const_ty.kind {
                        ty::FnDef(def_id, _) => Value::Function(def_id, ty),
                        _ => unreachable!(),
                    },

                    _ => Self::const_kind_to_value(constant.literal.val, ty)?,
                })
            }
        })
    }

    fn const_kind_to_value(const_kind: ConstKind<'tcx>, ty: Ty) -> InterpResult<'tcx, Value> {
        match const_kind {
            ConstKind::Value(ConstValue::Scalar(scalar)) => {
                Ok(Value::Const(scalar.to_bits(Size::from_bits(ty.bits().unwrap() as u64))?, ty))
            }
            ConstKind::Param(param) => Ok(Value::ConstParam(Param(param.index as usize, ty))),
            val => {
                Err(err_unsup_format!("Unsupported: {:?}", val).into())
            }
        }
    }

    #[allow(rustc::usage_of_qualified_ty)]
    fn transl_non_fn_ty(ty: ty::Ty<'tcx>) -> Option<Ty> {
        match ty.kind {
            ty::Bool => Some(Ty::Bool),
            ty::Int(int_ty) => {
                Some(Ty::Int(int_ty.bit_width().unwrap_or(8 * std::mem::size_of::<isize>())))
            }
            ty::Uint(uint_ty) => {
                Some(Ty::Uint(uint_ty.bit_width().unwrap_or(8 * std::mem::size_of::<usize>())))
            }
            _ => None,
        }
    }

    #[allow(rustc::usage_of_qualified_ty)]
    fn transl_ty(&self, ty: ty::Ty<'tcx>) -> InterpResult<'tcx, Ty> {
        match ty.kind {
            ty::FnDef(def_id, _) => self
                .tcx
                .optimized_mir(def_id)
                .local_decls
                .iter()
                .map(|ld| self.transl_ty(&ld.ty))
                .collect::<InterpResult<'_, Vec<Ty>>>()
                .map(|args_ty| Ty::Func(args_ty, Vec::new())),
            _ => Self::transl_non_fn_ty(ty)
                .ok_or_else(|| err_unsup_format!("Unsupported ty {:?}", ty).into()),
        }
    }

    fn fork_eval(&self, block: BasicBlock) -> InterpResult<'tcx, Expr> {
        let mut fork = Evaluator {
            memory: self.memory.clone(),
            location: block.start_location(),
            def_id: self.def_id,
            tcx: self.tcx,
        };

        fork.run()?;

        fork.memory.get(&Place::return_place()).map(|e| e.clone())
    }
}
