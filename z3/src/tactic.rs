use std::convert::TryFrom;
use std::ffi::CString;
use std::os::raw::c_uint;
use std::time::Duration;

use z3_sys::*;

use crate::{Context, HasContext, WrappedZ3, Goal, Params, Probe, Solver, make_z3_object};

make_z3_object! {
    /// Collection of subgoals resulting from applying of a tactic to a goal.
    pub struct ApplyResult<'ctx>
    where
        sys_ty: Z3_apply_result,
        inc_ref: Z3_apply_result_inc_ref,
        dec_ref: Z3_apply_result_dec_ref,
        to_str: Z3_apply_result_to_string,
    ;
}

impl<'ctx> ApplyResult<'ctx> {
    pub fn num_subgoals(&self) -> u32 {
        self.check_error_pass(unsafe { Z3_apply_result_get_num_subgoals(**self.ctx(), **self) }).unwrap()
    }

    pub fn list_subgoals(self) -> impl Iterator<Item = Goal<'ctx>> {
        (0..self.num_subgoals()).map(move |i| unsafe {
            Goal::wrap_check_error(
                self.ctx(),
                Z3_apply_result_get_subgoal(**self.ctx(), *self, i),
            )
        })
    }
}

make_z3_object! {
    /// Basic building block for creating custom solvers for specific problem domains.
    ///
    /// Z3 provides a variety of tactics, which can be queried via
    /// [`Tactic::list_all()`]. Individual tactics can be created via
    /// [`Tactic::new()`].
    ///
    /// Various combinators are available to combine tactics:
    ///
    /// - [`Tactic::repeat()`]
    /// - [`Tactic::try_for()`]
    /// - [`Tactic::and_then()`]
    /// - [`Tactic::or_else()`]
    /// - [`Tactic::probe_or_else()`]
    /// - [`Tactic::when()`]
    /// - [`Tactic::cond()`]
    ///
    /// Finally, a solver utilizing a tactic can be created via
    /// [`Tactic::solver()`].
    pub struct Tactic<'ctx>
    where
        sys_ty: Z3_tactic,
        inc_ref: Z3_tactic_inc_ref,
        dec_ref: Z3_tactic_dec_ref,
        to_str: Z3_tactic_get_help,
    ;
}

impl<'ctx> Tactic<'ctx> {
    /// Iterate through the valid tactic names.
    ///
    /// # Example
    ///
    /// ```
    /// # use z3::{Config, Context, Tactic};
    ///
    /// let ctx = Context::default();
    /// let tactics: Vec<_> = Tactic::list_all(&ctx).collect();
    /// assert!(tactics.contains(&"ufbv".to_string()));
    /// ```
    pub fn list_all(
        ctx: &'ctx Context,
    ) -> impl Iterator<Item = String> + 'ctx {
        (0..ctx.num_tactics()).map(move |n| {
            ctx.get_tactic_name(n)
        })
    }

    /// Create a tactic by name.
    ///
    /// # Example
    ///
    /// ```
    /// # use z3::{Config, Context, Tactic};
    ///
    /// let ctx = Context::default();
    /// let tactic = Tactic::new(&ctx, "nlsat");
    /// ```
    ///
    /// # See also
    ///
    /// - [`Tactic::list_all()`]
    pub fn new(ctx: &'ctx Context, name: &str) -> Tactic<'ctx> {
        let tactic_name = CString::new(name).unwrap();
        unsafe { Self::wrap_check_error(ctx, Z3_mk_tactic(**ctx, tactic_name.as_ptr())) }
    }

    /// Return a tactic that just return the given goal.
    pub fn create_skip(ctx: &'ctx Context) -> Tactic<'ctx> {
        unsafe { Self::wrap_check_error(ctx, Z3_tactic_skip(**ctx)) }
    }

    /// Return a tactic that always fails.
    pub fn create_fail(ctx: &'ctx Context) -> Tactic<'ctx> {
        unsafe { Self::wrap_check_error(ctx, Z3_tactic_fail(**ctx)) }
    }

    /// Return a tactic that keeps applying `t` until the goal is not modified anymore or the maximum
    /// number of iterations `max` is reached.
    pub fn repeat(ctx: &'ctx Context, t: &Tactic<'ctx>, max: u32) -> Tactic<'ctx> {
        unsafe { Self::wrap_check_error(ctx, Z3_tactic_repeat(**ctx, **t, max)) }
    }

    /// Return a tactic that applies the current tactic to a given goal, failing
    /// if it doesn't terminate within the period specified by `timeout`.
    pub fn try_for(&self, timeout: Duration) -> Tactic<'ctx> {
        let timeout_ms = c_uint::try_from(timeout.as_millis()).unwrap_or(c_uint::MAX);
        unsafe {
            Self::wrap_check_error(
                self.ctx(),
                Z3_tactic_try_for(**self.ctx(), **self, timeout_ms),
            )
        }
    }

    /// Return a tactic that applies the current tactic to a given goal and
    /// the `then_tactic` to every subgoal produced by the original tactic.
    pub fn and_then(&self, then_tactic: &Tactic<'ctx>) -> Tactic<'ctx> {
        unsafe {
            Self::wrap_check_error(
                self.ctx(),
                Z3_tactic_and_then(**self.ctx(), **self, **then_tactic),
            )
        }
    }

    /// Return a tactic that current tactic to a given goal,
    /// if it fails then returns the result of `else_tactic` applied to the given goal.
    pub fn or_else(&self, else_tactic: &Tactic<'ctx>) -> Tactic<'ctx> {
        unsafe {
            Self::wrap_check_error(
                self.ctx(),
                Z3_tactic_or_else(**self.ctx(), **self, **else_tactic),
            )
        }
    }

    /// Return a tactic that applies self to a given goal if the probe `p` evaluates to true,
    /// and `t` if `p` evaluates to false.
    pub fn probe_or_else(&self, p: &Probe<'ctx>, t: &Tactic<'ctx>) -> Tactic<'ctx> {
        unsafe {
            Self::wrap_check_error(
                self.ctx(),
                Z3_tactic_cond(**self.ctx(), **p, **self, **t),
            )
        }
    }

    /// Return a tactic that applies itself to a given goal if the probe `p` evaluates to true.
    /// If `p` evaluates to false, then the new tactic behaves like the skip tactic.
    pub fn when(&self, p: &Probe<'ctx>) -> Tactic<'ctx> {
        unsafe {
            Self::wrap_check_error(
                self.ctx(),
                Z3_tactic_when(**self.ctx(), **p, **self),
            )
        }
    }

    /// Return a tactic that applies `t1` to a given goal if the probe `p` evaluates to true,
    /// and `t2` if `p` evaluates to false.
    pub fn cond(
        ctx: &'ctx Context,
        p: &Probe<'ctx>,
        t1: &Tactic<'ctx>,
        t2: &Tactic<'ctx>,
    ) -> Tactic<'ctx> {
        unsafe {
            Self::wrap_check_error(
                ctx,
                Z3_tactic_cond(**ctx, **p, **t1, **t2),
            )
        }
    }

    /// Return a tactic that fails if the probe `p` evaluates to false.
    pub fn fail_if(ctx: &'ctx Context, p: &Probe<'ctx>) -> Tactic<'ctx> {
        unsafe { Self::wrap_check_error(ctx, Z3_tactic_fail_if(**ctx, **p)) }
    }

    /// Attempts to apply the tactic to `goal`. If the tactic succeeds, returns
    /// `Ok(_)` with a `ApplyResult`. If the tactic fails, returns `Err(_)` with
    /// an error message describing why.
    pub fn apply(
        &self,
        goal: &Goal<'ctx>,
        params: Option<&Params<'ctx>>,
    ) -> ApplyResult<'ctx> {
        unsafe {
            let z3_apply_result = match params {
                None => Z3_tactic_apply(**self.ctx(), **self, **goal),
                Some(params) => Z3_tactic_apply_ex(
                    **self.ctx(),
                    **self,
                    **goal,
                    **params,
                ),
            };
            ApplyResult::wrap_check_error(self.ctx(), z3_apply_result)
        }
    }

    /// Create a new solver that is implemented using the given tactic.
    ///
    /// # Example
    ///
    /// ```
    /// # use z3::{ast, Config, Context, SatResult, Tactic};
    ///
    /// let ctx = Context::default();
    /// let tactic = Tactic::new(&ctx, "qfnra");
    /// let solver = tactic.solver();
    ///
    /// let x = ast::Int::new_const(&ctx, "x");
    /// let y = ast::Int::new_const(&ctx, "y");
    ///
    /// solver.assert(&x.gt(&y));
    /// assert_eq!(solver.check(), SatResult::Sat);
    /// ```
    ///
    pub fn solver(&self) -> Solver<'ctx> {
        unsafe {
            Solver::wrap_check_error(
                self.ctx(),
                Z3_mk_solver_from_tactic(**self.ctx(), **self),
            )
        }
    }
}
