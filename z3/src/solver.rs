use std::ffi::{CStr, CString};
use std::ops::{AddAssign, Deref};
use std::ptr::NonNull;

use log::debug;

use z3_sys::*;

use crate::{Context, Model, Params, SatResult, Statistics, Symbol, AstVector, make_z3_object};
use crate::ast::{self, Ast};

make_z3_object! {
    /// (Incremental) solver, possibly specialized by a particular tactic or logic.
    pub struct Solver<'ctx>
    where
        sys_ty: Z3_solver,
        inc_ref: Z3_solver_inc_ref,
        dec_ref: Z3_solver_dec_ref,
        to_str: Z3_solver_to_string,
    ;
}

impl<'ctx> Solver<'ctx> {
    /// Create a new solver. This solver is a "combined solver"
    /// that internally uses a non-incremental (`solver1`) and an
    /// incremental solver (`solver2`). This combined solver changes
    /// its behaviour based on how it is used and how its parameters are set.
    ///
    /// If the solver is used in a non incremental way (i.e. no calls to
    /// [`Solver::push()`] or [`Solver::pop()`], and no calls to
    /// [`Solver::assert()`] or [`Solver::assert_and_track()`] after checking
    /// satisfiability without an intervening [`Solver::reset()`]) then `solver1`
    /// will be used. This solver will apply Z3's "default" tactic.
    ///
    /// The "default" tactic will attempt to probe the logic used by the
    /// assertions and will apply a specialized tactic if one is supported.
    /// Otherwise the general `(and-then simplify smt)` tactic will be used.
    ///
    /// If the solver is used in an incremental way then the combined solver
    /// will switch to using `solver2` (which behaves similarly to the general
    /// "smt" tactic).
    ///
    /// Note however it is possible to set the `solver2_timeout`,
    /// `solver2_unknown`, and `ignore_solver1` parameters of the combined
    /// solver to change its behaviour.
    ///
    /// The function [`Solver::get_model()`] retrieves a model if the
    /// assertions is satisfiable (i.e., the result is
    /// `SatResult::Sat`) and [model construction is enabled].
    /// The function [`Solver::get_model()`] can also be used even
    /// if the result is `SatResult::Unknown`, but the returned model
    /// is not guaranteed to satisfy quantified assertions.
    ///
    /// [model construction is enabled]: crate::Config::set_model_generation
    pub fn new(ctx: &'ctx Context) -> Self {
        unsafe { Self::wrap_check_error(ctx, Z3_mk_solver(*ctx)) }
    }

    /// Parse an SMT-LIB2 string with assertions, soft constraints and optimization objectives.
    /// Add the parsed constraints and objectives to the solver.
    pub fn from_smtlib(&self, source: impl Into<Vec<[u8]>>) {
        let source_cstring = CString::new(source).unwrap();
        let p = self.check_error_ptr(unsafe {
            Z3_solver_from_string(*self.ctx(), *self, source_cstring.as_ptr());
        }).unwrap();
    }

    /// Create a new solver customized for the given logic.
    /// It returns `None` if the logic is unknown or unsupported.
    pub fn new_for_logic<S: Into<Symbol>>(ctx: &'ctx Context, logic: S) -> Option<Self> {
        let sym = logic.into().as_z3_symbol(ctx);
        let p = self.check_error_ptr( unsafe { Z3_mk_solver_for_logic(*ctx, logic.into().as_z3_symbol(ctx)) } ).ok()?;
        unsafe { Self::wrap(ctx, p) }
    }

    pub fn translate<'dest_ctx>(&self, dest: &'dest_ctx Context) -> Solver<'dest_ctx> {
        unsafe {
            Solver::wrap(
                dest,
                self.check_error_ptr(Z3_solver_translate(*self.ctx(), *self, *dest)).unwrap(),
            )
        }
    }

    /// Assert a constraint into the solver.
    ///
    /// The functions [`Solver::check()`] and [`Solver::check_assumptions()`]
    /// should be used to check whether the logical context is consistent
    /// or not.
    ///
    /// ```rust
    /// use z3::{Config, Context, Solver, ast, SatResult, ast::Bool};
    /// let cfg = Config::new();
    /// let ctx = Context::new(&cfg);
    /// let mut solver = Solver::new(&ctx);
    ///
    /// solver.assert(&Bool::from_bool(&ctx, true));
    /// solver += &Bool::from_bool(&ctx, false);
    /// solver += Bool::fresh_const(&ctx, "");
    ///
    /// assert_eq!(solver.check(), SatResult::Unsat);
    /// ````
    ///
    /// # See also:
    ///
    /// - [`Solver::assert_and_track()`]
    pub fn assert(&self, ast: &ast::Bool<'ctx>) {
        debug!("assert: {:?}", ast);
        unsafe { Z3_solver_assert(*self.ctx(), *self, *ast) };
        self.check_error().unwrap();
    }

    /// Assert a constraint `a` into the solver, and track it (in the
    /// unsat) core using the Boolean constant `p`.
    ///
    /// This API is an alternative to
    /// [`Solver::check_assumptions()`]
    /// for extracting unsat cores. Both APIs can be used in the same solver.
    /// The unsat core will contain a combination of the Boolean variables
    /// provided using [`Solver::assert_and_track()`]
    /// and the Boolean literals provided using
    /// [`Solver::check_assumptions()`].
    ///
    /// # See also:
    ///
    /// - [`Solver::assert()`]
    pub fn assert_and_track(&self, ast: &ast::Bool<'ctx>, p: &ast::Bool<'ctx>) {
        debug!("assert_and_track: {:?}", ast);
        unsafe { Z3_solver_assert_and_track(*self.ctx(), *self, ast.z3_ast, p.z3_ast) };
        self.check_error().unwrap();
    }

    /// Remove all assertions from the solver.
    pub fn reset(&self) {
        unsafe { Z3_solver_reset(*self.ctx(), *self) };
        self.check_error().unwrap();
    }

    /// Check whether the assertions in a given solver are consistent or not.
    ///
    /// The function [`Solver::get_model()`]
    /// retrieves a model if the assertions is satisfiable (i.e., the
    /// result is [`SatResult::Sat`]) and [model construction is enabled].
    /// Note that if the call returns `SatResult::Unknown`, Z3 does not
    /// ensure that calls to [`Solver::get_model()`]
    /// succeed and any models produced in this case are not guaranteed
    /// to satisfy the assertions.
    ///
    /// The function [`Solver::get_proof()`]
    /// retrieves a proof if [proof generation was enabled] when the context
    /// was created, and the assertions are unsatisfiable (i.e., the result
    /// is [`SatResult::Unsat`]).
    ///
    /// # See also:
    ///
    /// - [`Config::set_model_generation()`](crate::Config::set_model_generation)
    /// - [`Config::set_proof_generation()`](crate::Config::set_proof_generation)
    /// - [`Solver::check_assumptions()`]
    ///
    /// [model construction is enabled]: crate::Config::set_model_generation
    /// [proof generation was enabled]: crate::Config::set_proof_generation
    pub fn check(&self) -> SatResult {
        match self.check_error_pass(unsafe { Z3_solver_check(*self.ctx(), *self) }).unwrap() {
            Z3_L_FALSE => SatResult::Unsat,
            Z3_L_UNDEF => SatResult::Unknown,
            Z3_L_TRUE => SatResult::Sat,
            _ => unreachable!(),
        }
    }

    /// Check whether the assertions in the given solver and
    /// optional assumptions are consistent or not.
    ///
    /// The function [`Solver::get_unsat_core()`]
    /// retrieves the subset of the assumptions used in the
    /// unsatisfiability proof produced by Z3.
    ///
    /// # See also:
    ///
    /// - [`Solver::check()`]
    pub fn check_assumptions(&self, assumptions: &[ast::Bool<'ctx>]) -> SatResult {
        let a: Vec<NonNull<Z3_ast>> = assumptions.iter().map(Deref::deref).collect();
        let len:u32 = a.len().try_into().unwrap();
        let res = unsafe {
            Z3_solver_check_assumptions(*self.ctx(), *self, len, a.as_ptr())
        };
        self.check_error().unwrap();
        match res {
            Z3_L_FALSE => SatResult::Unsat,
            Z3_L_UNDEF => SatResult::Unknown,
            Z3_L_TRUE => SatResult::Sat,
            _ => unreachable!(),
        }
    }

    // Return a vector of assumptions in the solver.
    pub fn get_assertions(&self) -> Vec<ast::Bool<'ctx>> {
        let z3_vec = self.check_error_ptr(unsafe { Z3_solver_get_assertions(*self.ctx(), *self) }).unwrap();
        let vec = unsafe {AstVector::wrap(&self.ctx(), z3_vec)};
        vec.iter().map(|ast| ast.as_bool().unwrap()).collect()
    }

    /// Return a subset of the assumptions provided to either the last
    ///
    /// * [`Solver::check_assumptions`] call, or
    /// * sequence of [`Solver::assert_and_track`] calls followed
    ///   by a [`Solver::check`] call.
    ///
    /// These are the assumptions Z3 used in the unsatisfiability proof.
    /// Assumptions are available in Z3. They are used to extract unsatisfiable
    /// cores.  They may be also used to "retract" assumptions. Note that,
    /// assumptions are not really "soft constraints", but they can be used to
    /// implement them.
    ///
    /// By default, the unsat core will not be minimized. Generation of a minimized
    /// unsat core can be enabled via the `"sat.core.minimize"` and `"smt.core.minimize"`
    /// settings for SAT and SMT cores respectively. Generation of minimized unsat cores
    /// will be more expensive.
    ///
    /// # See also:
    ///
    /// - [`Solver::check_assumptions`]
    /// - [`Solver::assert_and_track`]
    pub fn get_unsat_core(&self) -> Vec<ast::Bool<'ctx>> {
        let p = unsafe { Z3_solver_get_unsat_core(*self.ctx(), *self) };
        let p = match self.check_error_ptr(p) {
            Ok(v) => v,
            Err(_) => return vec![],
        };
        let zvec = unsafe { AstVector::wrap(*self.ctx(), p) };
        zvec.iter().map(|ast| ast.as_bool().unwrap()).collect()
    }

    /// Retrieve consequences from the solver given a set of assumptions.
    pub fn get_consequences(
        &self,
        assumptions: &[ast::Bool<'ctx>],
        variables: &[ast::Bool<'ctx>],
    ) -> Vec<ast::Bool<'ctx>> {
        let assumptions_z = AstVector::new();
        for ast in assumptions {
            assumptions_z.push(ast.into());
        }
        let variables_z = AstVector::new();
        for ast in variables {
            variables_z.push(ast.into());
        }
        let consequences_z = AstVector::new();
        self.check_error_bool(unsafe { Z3_solver_get_consequences(
            *self.ctx(),
            *self,
            *assumptions_z,
            *variables_z,
            *consequences_z,
        )}).unwrap();
        consequences_z.iter().map(|ast| ast.as_bool().unwrap()).collect()
    }

    /// Create a backtracking point.
    ///
    /// The solver contains a stack of assertions.
    ///
    /// # See also:
    ///
    /// - [`Solver::pop()`]
    pub fn push(&self) {
        unsafe { Z3_solver_push(*self.ctx(), *self) };
        self.check_error().unwrap()
    }

    /// Backtrack `n` backtracking points.
    ///
    /// # See also:
    ///
    /// - [`Solver::push()`]
    pub fn pop(&self, n: u32) {
        unsafe { Z3_solver_pop(*self.ctx(), *self, n) };
        self.check_error.unwrap();
    }

    /// Retrieve the model for the last [`Solver::check()`]
    /// or [`Solver::check_assumptions()`].
    ///
    /// The error handler is invoked if a model is not available because
    /// the commands above were not invoked for the given solver, or if
    /// the result was [`SatResult::Unsat`].
    pub fn get_model(&self) -> Option<Model<'ctx>> {
        Model::of_solver(self)
    }

    /// Retrieve the proof for the last [`Solver::check()`]
    /// or [`Solver::check_assumptions()`].
    ///
    /// The error handler is invoked if [proof generation is not enabled],
    /// or if the commands above were not invoked for the given solver,
    /// or if the result was different from [`SatResult::Unsat`].
    ///
    /// # See also:
    ///
    /// - [`Config::set_proof_generation()`](crate::Config::set_proof_generation)
    ///
    /// [proof generation is not enabled]: crate::Config::set_proof_generation
    //
    // This seems to actually return an Ast with kind `SortKind::Unknown`, which we don't
    // have an Ast subtype for yet.
    pub fn get_proof(&self) -> Option<ast::Dynamic<'ctx>> {
        let m = unsafe { Z3_solver_get_proof(*self.ctx(), *self) };
        let m = self.check_error_ptr(m).ok()?;
        Some(unsafe { ast::Dynamic::wrap(self.ctx(), m) })
    }

    /// Return a brief justification for an "unknown" result (i.e.,
    /// [`SatResult::Unknown`]) for the commands [`Solver::check()`]
    /// and [`Solver::check_assumptions()`].
    pub fn get_reason_unknown(&self) -> Option<String> {
        let p = unsafe { Z3_solver_get_reason_unknown(*self.ctx(), *self) };
        let p = self.check_error_ptr(p).ok()?;
        unsafe { CStr::from_ptr(p) }
            .to_str()
            .ok()
            .map(|s| s.to_string())
    }

    /// Set the current solver using the given parameters.
    pub fn set_params(&self, params: &Params<'ctx>) {
        unsafe { Z3_solver_set_params(*self.ctx(), *self, params.z3_params) };
        self.check_error();
    }

    /// Retrieve the statistics for the last [`Solver::check()`].
    pub fn get_statistics(&self) -> Statistics<'ctx> {
        unsafe {
            Statistics::wrap_check_error(
                self.ctx(),
                Z3_solver_get_statistics(*self.ctx(), *self),
            )
        }
    }
}

impl<'ctx> AddAssign<&ast::Bool<'ctx>> for Solver<'ctx> {
    fn add_assign(&mut self, rhs: &ast::Bool<'ctx>) {
        self.assert(rhs);
    }
}

impl<'ctx> AddAssign<ast::Bool<'ctx>> for Solver<'ctx> {
    fn add_assign(&mut self, rhs: ast::Bool<'ctx>) {
        self.assert(&rhs);
    }
}
