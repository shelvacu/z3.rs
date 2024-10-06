use log::debug;
use std::convert::TryInto;
use std::ptr::NonNull;
use std::ffi::{CStr, CString};

use z3_sys::*;

use crate::{
    ast::{Ast, Bool, Dynamic},
    Context, HasContext, WrappedZ3, Model, Params, SatResult, Statistics, Symbol, AstVector,
    make_z3_object,
};

use num::{
    bigint::{BigInt, BigUint, Sign},
    rational::BigRational,
};

make_z3_object! {
    pub struct Optimize<'ctx>
    where
        sys_ty: Z3_optimize,
        inc_ref: Z3_optimize_inc_ref,
        dec_ref: Z3_optimize_dec_ref,
        to_str: Z3_optimize_to_string,
    ;
}

impl<'ctx> Optimize<'ctx> {
    /// Create a new optimize context.
    pub fn new(ctx: &'ctx Context) -> Optimize<'ctx> {
        unsafe { Self::wrap_check_error(ctx, Z3_mk_optimize(**ctx)) }
    }

    /// Parse an SMT-LIB2 string with assertions, soft constraints and optimization objectives.
    /// Add the parsed constraints and objectives to the optimizer.
    pub fn from_string<T: Into<Vec<u8>>>(&self, source_string: T) {
        let source_cstring = CString::new(source_string).unwrap();
        unsafe {
            Z3_optimize_from_string(**self.ctx(), **self, source_cstring.as_ptr());
        }
        self.check_error().unwrap();
    }

    /// Assert hard constraint to the optimization context.
    ///
    /// # See also:
    ///
    /// - [`Optimize::assert_soft()`]
    /// - [`Optimize::maximize()`]
    /// - [`Optimize::minimize()`]
    pub fn assert(&self, ast: &impl Ast<'ctx>) {
        unsafe { Z3_optimize_assert(**self.ctx(), **self, **ast) };
        self.check_error().unwrap();
    }

    /// Assert a constraint `a` into the solver, and track it (in the
    /// unsat) core using the Boolean constant `p`.
    ///
    /// This API is an alternative to
    /// [`Optimize::check()`]
    /// for extracting unsat cores. Both APIs can be used in the same solver.
    /// The unsat core will contain a combination of the Boolean variables
    /// provided using [`Optimize::assert_and_track()`]
    /// and the Boolean literals provided using
    /// [`Optimize::check()`].
    ///
    /// # See also:
    ///
    /// - [`Optimize::assert()`]
    /// - [`Optimize::assert_soft()`]
    pub fn assert_and_track(&self, ast: &Bool<'ctx>, p: &Bool<'ctx>) {
        debug!("assert_and_track: {:?}", ast);
        unsafe { Z3_optimize_assert_and_track(**self.ctx(), **self, **ast, **p) };
        self.check_error().unwrap();
    }

    /// Assert soft constraint to the optimization context.
    /// Weight is a positive, rational penalty for violating the constraint.
    /// Group is an optional identifier to group soft constraints.
    ///
    /// # See also:
    ///
    /// - [`Optimize::assert()`]
    /// - [`Optimize::maximize()`]
    /// - [`Optimize::minimize()`]
    pub fn assert_soft(&self, ast: &impl Ast<'ctx>, weight: impl Weight, group: Option<Symbol>) {
        let weight_string = weight.to_string();
        let weight_cstring = CString::new(weight_string).unwrap();
        let group: *mut Z3_symbol = group
            .map(|g| g.as_z3_symbol(self.ctx()).as_ptr())
            .unwrap_or(std::ptr::null_mut());
        unsafe {
            Z3_optimize_assert_soft(
                **self.ctx(),
                **self,
                **ast,
                weight_cstring.as_ptr(),
                group,
            )
        };
        self.check_error().unwrap();
    }

    /// Add a maximization constraint.
    ///
    /// # See also:
    ///
    /// - [`Optimize::assert()`]
    /// - [`Optimize::minimize()`]
    pub fn maximize(&self, ast: &impl Ast<'ctx>) {
        // https://github.com/Z3Prover/z3/blob/09f911d8a84cd91988e5b96b69485b2a9a2edba3/src/opt/opt_context.cpp#L118-L120
        assert!(matches!(
            ast.sort().sort_kind(),
            SortKind::Int | SortKind::Real | SortKind::BV
        ));
        unsafe { Z3_optimize_maximize(**self.ctx(), **self, **ast) };
        self.check_error().unwrap();
    }

    /// Add a minimization constraint.
    ///
    /// # See also:
    ///
    /// - [`Optimize::assert()`]
    /// - [`Optimize::maximize()`]
    pub fn minimize(&self, ast: &impl Ast<'ctx>) {
        assert!(matches!(
            ast.sort().sort_kind(),
            SortKind::Int | SortKind::Real | SortKind::BV
        ));
        unsafe { Z3_optimize_minimize(**self.ctx(), **self, **ast) };
        self.check_error().unwrap();
    }

    /// Return a subset of the assumptions provided to either the last
    ///
    /// * [`Optimize::check`] call, or
    /// * sequence of [`Optimize::assert_and_track`] calls followed
    ///   by an [`Optimize::check`] call.
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
    /// - [`Optimize::check`]
    pub fn get_unsat_core(&self) -> Vec<Bool<'ctx>> {
        let z3_unsat_core = unsafe { Z3_optimize_get_unsat_core(**self.ctx(), **self) };
        self.check_error().unwrap();
        let z3_unsat_core = match NonNull::new(z3_unsat_core) {
            Some(v) => v,
            None => return vec![],
        };
        let z3_unsat_core = unsafe { AstVector::wrap(self.ctx(), z3_unsat_core) };
        z3_unsat_core.iter().map(|i| i.as_bool().unwrap()).collect()
    }

    /// Create a backtracking point.
    ///
    /// The optimize solver contains a set of rules, added facts and assertions.
    /// The set of rules, facts and assertions are restored upon calling
    /// [`Optimize::pop()`].
    ///
    /// # See also:
    ///
    /// - [`Optimize::pop()`]
    pub fn push(&self) {
        unsafe { Z3_optimize_push(**self.ctx(), **self) };
        self.check_error().unwrap();
    }

    /// Backtrack one level.
    ///
    /// # Preconditions:
    ///
    /// - The number of calls to [`Optimize::pop`] cannot exceed the number of calls to
    ///   [`Optimize::push()`].
    ///
    /// # See also:
    ///
    /// - [`Optimize::push()`]
    pub fn pop(&self) {
        unsafe { Z3_optimize_pop(**self.ctx(), **self) };
        self.check_error().unwrap();
    }

    /// Check consistency and produce optimal values.
    ///
    /// # See also:
    ///
    /// - [`Optimize::get_model()`]
    pub fn check(&self, assumptions: &[&Bool<'ctx>]) -> SatResult {
        let assumptions: Vec<NonNull<Z3_ast>> = assumptions.iter().map(|a| ***a).collect();
        match self.check_error_pass(unsafe {
            Z3_optimize_check(
                **self.ctx(),
                **self,
                assumptions.len().try_into().unwrap(),
                assumptions.as_ptr(),
            )
        }).unwrap() {
            Z3_L_FALSE => SatResult::Unsat,
            Z3_L_UNDEF => SatResult::Unknown,
            Z3_L_TRUE => SatResult::Sat,
        }
    }

    /// Retrieve the model for the last [`Optimize::check()`].
    ///
    /// The error handler is invoked if a model is not available because
    /// the commands above were not invoked for the given optimization
    /// solver, or if the result was [`SatResult::Unsat`].
    pub fn get_model(&self) -> Option<Model<'ctx>> {
        Model::of_optimize(self)
    }

    /// Retrieve the objectives for the last [`Optimize::check()`].
    ///
    /// This contains maximize/minimize objectives and grouped soft constraints.
    pub fn get_objectives(&self) -> Vec<Dynamic<'ctx>> {
        let objectives_z = unsafe { AstVector::wrap_check_error(self.ctx(), Z3_optimize_get_objectives(**self.ctx(), **self)) };
        objectives_z.iter().collect()
    }

    /// Retrieve a string that describes the last status returned by [`Optimize::check()`].
    ///
    /// Use this method when [`Optimize::check()`] returns [`SatResult::Unknown`].
    pub fn get_reason_unknown(&self) -> Option<String> {
        let p = unsafe { Z3_optimize_get_reason_unknown(**self.ctx(), **self) };
        self.check_error().unwrap();
        if p.is_null() {
            return None;
        }
        unsafe { CStr::from_ptr(p) }
            .to_str()
            .ok()
            .map(|s| s.to_string())
    }

    /// Configure the parameters for this Optimize.
    pub fn set_params(&self, params: &Params<'ctx>) {
        unsafe { Z3_optimize_set_params(**self.ctx(), **self, **params) };
        self.check_error().unwrap();
    }

    /// Retrieve the statistics for the last [`Optimize::check()`].
    pub fn get_statistics(&self) -> Statistics<'ctx> {
        unsafe {
            Statistics::wrap_check_error(
                self.ctx(),
                Z3_optimize_get_statistics(**self.ctx(), **self),
            )
        }
    }
}

/// A rational non-negative weight for soft assertions.
/// This trait is sealed and cannot be implemented for types outside of
/// `z3`.
///
/// # See also:
///
/// - [`Optimize::assert_soft()`]
pub trait Weight: private::Sealed {
    /// This is purposefully distinct from `ToString` to allow
    /// specifying a `to_string` for tuples.
    fn to_string(&self) -> String;
}

macro_rules! impl_weight {
    ($($ty: ty),*) => {
        $(
            impl Weight for $ty {
                fn to_string(&self) -> String {
                    ToString::to_string(&self)
                }
            }

            impl Weight for ($ty, $ty) {
                fn to_string(&self) -> String {
                    format!("{} / {}", self.0, self.1)
                }
            }
        )*
    };
}

impl_weight! {
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
}

impl Weight for BigInt {
    fn to_string(&self) -> String {
        assert_ne!(self.sign(), Sign::Minus);
        self.to_str_radix(10)
    }
}

impl Weight for BigUint {
    fn to_string(&self) -> String {
        self.to_str_radix(10)
    }
}

impl Weight for BigRational {
    fn to_string(&self) -> String {
        assert_ne!(self.numer().sign(), Sign::Minus);
        assert_ne!(self.denom().sign(), Sign::Minus);
        format!(
            "{} / {}",
            self.numer().to_str_radix(10),
            self.denom().to_str_radix(10)
        )
    }
}

macro_rules! impl_sealed {
    ($($ty: ty),*) => {
        mod private {
            #[allow(unused_imports)]
            use super::*;
            pub trait Sealed {}
            $(
                impl Sealed for $ty {}
                impl Sealed for ($ty, $ty) {}
            )*

            impl Sealed for BigInt {}
            impl Sealed for BigUint {}
            impl Sealed for BigRational {}
        }
    };
}

impl_sealed! {
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
}
