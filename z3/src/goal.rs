use std::ffi::CStr;

use z3_sys::*;

use crate::{Context, HasContext, make_z3_object};
use crate::ast::{self, Ast, Bool, Dynamic, unop, binop, trinop, varop};

make_z3_object! {
    /// Set of formulas that can be solved and/or transformed using tactics and solvers.
    pub struct Goal<'ctx>
    where
        sys_ty: Z3_goal,
        inc_ref: Z3_goal_inc_ref,
        dec_ref: Z3_goal_dec_ref,
        to_str: Z3_goal_to_string,
    ;
}

impl<'ctx> Goal<'ctx> {
    /// NOTE: The Z3 context ctx must have been created with proof generation support.
    pub fn new(ctx: &'ctx Context, models: bool, unsat_cores: bool, proofs: bool) -> Goal<'ctx> {
        unsafe { Self::wrap_check_error(ctx, Z3_mk_goal(*ctx, models, unsat_cores, proofs)) }
    }

    /// Add a new formula `a` to the given goal.
    pub fn assert(&self, ast: &Bool<'ctx>) {
        unsafe { Z3_goal_assert(*self.ctx(), *self, *ast) };
        self.check_error().unwrap();
    }

    /// Return true if the given goal contains the formula `false`.
    pub fn is_inconsistent(&self) -> bool {
        self.check_error_pass(unsafe { Z3_goal_inconsistent(*self.ctx(), *self) }).unwrap()
    }

    /// Return the depth of the given goal. It tracks how many transformations were applied to it.
    pub fn get_depth(&self) -> u32 {
        self.check_error_pass(unsafe { Z3_goal_depth(*self.ctx(), *self) }).unwrap()
    }

    /// Return the number of formulas in the given goal.
    pub fn get_size(&self) -> u32 {
        self.check_error_pass(unsafe { Z3_goal_size(*self.ctx(), *self) }).unwrap()
    }

    /// Return the number of formulas, subformulas and terms in the given goal.
    pub fn get_num_expr(&self) -> u32 {
        self.check_error_pass(unsafe { Z3_goal_num_exprs(*self.ctx(), *self) }).unwrap()
    }

    /// Return true if the goal is empty, and it is precise or the product of a under approximation.
    pub fn is_decided_sat(&self) -> bool {
        self.check_error_pass(unsafe { Z3_goal_is_decided_sat(*self.ctx(), *self) }).unwrap()
    }
    /// Return true if the goal contains false, and it is precise or the product of an over approximation.
    pub fn is_decided_unsat(&self) -> bool {
        self.check_error_pass(unsafe { Z3_goal_is_decided_unsat(*self.ctx(), *self) }).unwrap()
    }

    /// Erase all formulas from the given goal.
    pub fn reset(&self) {
        unsafe { Z3_goal_reset(*self.ctx(), *self) };
        self.check_error();
    }

    /// Copy a goal `g` from its current context to the context `target`.
    #[allow(clippy::needless_lifetimes)]
    pub fn translate<'dest_ctx>(self, target: &'dest_ctx Context) -> Goal<'dest_ctx> {
        unsafe {
            Goal::wrap_check_error(
                target,
                Z3_goal_translate(*self.ctx(), *self, *target),
            )
        }
    }

    /// Return the "precision" of the given goal. Goals can be transformed using over and under approximations.
    pub fn get_precision(&self) -> GoalPrec {
        self.check_error_pass(unsafe { Z3_goal_precision(*self.ctx(), *self) }).unwrap()
    }

    pub fn iter_formulas<'a>(&'a self) -> impl Iterator<Item = Dynamic<'ctx>> + 'a
    {
        let goal_size = self.get_size();
        let z3_ctx = *self.ctx();
        let z3_goal = *self;
        (0..goal_size).map(move |i| {
            let formula = unsafe { Z3_goal_formula(z3_ctx, z3_goal, i) };
            let formula = self.check_error_ptr(formula).unwrap();
            unsafe { Dynamic::wrap(self.ctx, formula) }
        })
    }

    /// Return a vector of the formulas from the given goal.
    pub fn get_formulas(&self) -> Vec<Dynamic<'ctx>>
    {
        self.iter_formulas().collect()
    }
}
