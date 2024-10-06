//! # Z3
//!
//! Z3 is a theorem prover [from Microsoft Research](https://github.com/Z3Prover/z3/).

#![allow(clippy::unreadable_literal)]
#![warn(clippy::doc_markdown)]
#![deny(missing_debug_implementations)]

use std::ptr::NonNull;
use std::ffi::CStr;
use std::ops::Deref;
use z3_sys::*;
use crate::error::*;
pub use z3_sys::{AstKind, GoalPrec, SortKind};

pub mod ast;
mod config;
mod context;
pub mod datatype_builder;
pub mod error;
mod goal;
mod model;
mod ops;
mod optimize;
mod params;
mod probe;
mod solver;
mod statistics;
mod symbol;
mod tactic;
mod version;
mod ast_vector;
mod func_entry;
mod func_interp;

pub use crate::params::{get_global_param, reset_all_global_params, set_global_param};
pub use crate::version::{full_version, version, Version};

pub use config::Config;

pub use context::{Context, ContextHandle};

macro_rules! make_z3_object {
    (
        $(#[$struct_meta:meta])*
        $v:vis struct $name:ident < 'ctx >
        where
            sys_ty: $sys_ty:ident,
            inc_ref: $inc_ref:ident,
            dec_ref: $dec_ref:ident,
            $(to_str: $to_str:ident,)?
        ;
    ) => {
        $(#[$struct_meta])*
        $v struct $name<'ctx> {
            _ctx: &'ctx $crate::Context,
            _ptr: ::std::ptr::NonNull<$sys_ty>,
        }

        impl<'ctx> $crate::WrappedZ3<'ctx> for $name<'ctx> {
            type Pointed = $sys_ty;

            /// Wraps a raw [`$sys_ty`]
            ///
            /// Nearly every function in z3-sys has the possibility of returning null and setting
            /// an error code. Make sure to use one of the check_error_* methods before wrapping
            /// the return value.
            ///
            /// The reference counter will be incremented, and decremented with Drop
            ///
            /// ### Safety
            ///
            /// `ptr` must be a valid pointer to a [`$sys_ty`]
            unsafe fn wrap(ctx: &'ctx $crate::Context, ptr: ::std::ptr::NonNull<$sys_ty>) -> Self {
                $inc_ref(**ctx, ptr);
                $crate::HasContext::check_error(&ctx).unwrap();
                Self {
                    _ctx: ctx,
                    _ptr: ptr,
                }
            }
        }

        impl<'ctx> $crate::HasContext<'ctx> for $name<'ctx> {
            fn ctx(&self) -> &'ctx $crate::Context {
                self._ctx
            }
        }

        impl<'ctx> ::std::ops::Deref for $name<'ctx> {
            type Target = ::std::ptr::NonNull<$sys_ty>;

            fn deref(&self) -> &Self::Target {
                &self._ptr
            }
        }

        impl<'ctx> ::std::clone::Clone for $name<'ctx> {
            fn clone(&self) -> Self {
                unsafe { <Self as $crate::WrappedZ3>::wrap(self._ctx, **self) }
            }
        }

        impl<'ctx> ::std::ops::Drop for $name<'ctx> {
            fn drop(&mut self) {
                unsafe { $dec_ref(**self._ctx, **self) };
                // panic!ing in drop is annoying, so don't do that, so don't call check_error since we're not going to do anything with the result
            }
        }

        $(
        impl<'ctx> ::std::fmt::Debug for $name<'ctx> {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                let msg = $crate::HasContext::check_error_str(self, unsafe { $to_str(**self._ctx, self._ptr) }).map_err(|_| ::std::fmt::Error)?;
                write!(f, "{}({})", stringify!($name), msg)
            }
        }
        )?
    };
}

pub(crate) use make_z3_object;

pub trait WrappedZ3<'ctx>: HasContext<'ctx> + Deref<Target = NonNull<Self::Pointed>> {
    type Pointed;

    unsafe fn wrap(ctx: &'ctx Context, ptr: NonNull<Self::Pointed>) -> Self
    where
        Self: Sized
    ;

    unsafe fn wrap_check_error(ctx: &'ctx Context, ptr: *mut Self::Pointed) -> Self
    where
        Self: Sized
    {
        let p = ctx.check_error_ptr(ptr).unwrap();
        unsafe { Self::wrap(ctx, p) }
    }
}

pub use ast::IsNotApp;
pub use ast_vector::AstVector;
pub use model::Model;
pub use optimize::Optimize;
pub use symbol::Symbol;
pub use solver::Solver;
pub use func_interp::FuncInterp;

pub use z3_sys::DeclKind;

/// Build a custom [datatype sort](DatatypeSort).
///
/// Example:
/// ```
/// # use z3::{ast::Int, Config, Context, DatatypeAccessor, DatatypeBuilder, SatResult, Solver, Sort, ast::{Ast, Datatype}};
/// # let cfg = Config::new();
/// # let ctx = Context::new(&cfg);
/// # let solver = Solver::new(&ctx);
/// // Like Rust's Option<int> type
/// let option_int = DatatypeBuilder::new(&ctx, "OptionInt")
/// .variant("None", vec![])
/// .variant(
///     "Some",
///     vec![("value", DatatypeAccessor::Sort(Sort::int(&ctx)))],
/// )
/// .finish();
///
/// // Assert x.is_none()
/// let x = Datatype::new_const(&ctx, "x", &option_int.sort);
/// solver.assert(&option_int.variants[0].tester.apply(&[&x]).as_bool().unwrap());
///
/// // Assert y == Some(3)
/// let y = Datatype::new_const(&ctx, "y", &option_int.sort);
/// let value = option_int.variants[1].constructor.apply(&[&Int::from_i64(&ctx, 3)]);
/// solver.assert(&y._eq(&value.as_datatype().unwrap()));
///
/// assert_eq!(solver.check(), SatResult::Sat);
/// let model = solver.get_model().unwrap();;
///
/// // Get the value out of Some(3)
/// let ast = option_int.variants[1].accessors[0].apply(&[&y]);
/// assert_eq!(3, model.eval(&ast.as_int().unwrap(), true).unwrap().as_i64().unwrap());
/// ```
#[derive(Debug)]
pub struct DatatypeBuilder<'ctx> {
    ctx: &'ctx Context,
    name: Symbol,
    constructors: Vec<(String, Vec<(String, DatatypeAccessor<'ctx>)>)>,
}

/// Wrapper which can point to a sort (by value) or to a custom datatype (by name).
#[derive(Debug)]
pub enum DatatypeAccessor<'ctx> {
    Sort(ast::Sort<'ctx>),
    Datatype(Symbol),
}

/// Inner variant for a custom [datatype sort](DatatypeSort).
#[derive(Debug)]
pub struct DatatypeVariant<'ctx> {
    pub constructor: ast::FuncDecl<'ctx>,
    pub tester: ast::FuncDecl<'ctx>,
    pub accessors: Vec<ast::FuncDecl<'ctx>>,
}

/// A custom datatype sort.
#[derive(Debug)]
pub struct DatatypeSort<'ctx> {
    pub sort: ast::Sort<'ctx>,
    pub variants: Vec<DatatypeVariant<'ctx>>,
}

/// Parameter set used to configure many components (simplifiers, tactics, solvers, etc).
pub struct Params<'ctx> {
    ctx: &'ctx Context,
    z3_params: NonNull<Z3_params>,
}

/// Result of a satisfiability query.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SatResult {
    /// The query is unsatisfiable.
    Unsat,
    /// The query was interrupted, timed out or otherwise failed.
    Unknown,
    /// The query is satisfiable.
    Sat,
}

pub trait HasContext<'ctx> {
    fn ctx(&self) -> &'ctx Context;

    fn check_error_ptr<T: ?Sized>(&self, ptr: *mut T) -> Result<NonNull<T>, Error> {
        self.check_error().map(|_| NonNull::new(ptr).expect("Result code Ok but null ptr passed in"))
    }

    fn check_error_pass<T>(&self, thing: T) -> Result<T, Error> {
        self.check_error().map(|_| thing)
    }

    fn check_error_bool(&self, result: bool) -> bool {
        self.check_error().is_ok() && result
    }

    fn check_error(&self) -> Result<(), Error> {
        let code = self.get_error_code();
        if code == ErrorCode::OK {
            return Ok(());
        }
        let msg = self.get_error_message(code);
        Err(Error{code, msg})
    }

    fn check_error_str(&self, s: Z3_string) -> Result<String, Error> {
        self.check_error()?;
        assert!(!s.is_null());
        Ok(unsafe { CStr::from_ptr(s) }.to_str().unwrap().to_string())
    }

    fn get_error_code(&self) -> ErrorCode {
        unsafe { Z3_get_error_code(**self.ctx()) }
    }

    fn get_error_message(&self, err_code: ErrorCode) -> String {
        let msg_cstr = unsafe { CStr::from_ptr(Z3_get_error_msg(**self.ctx(), err_code)) };
        msg_cstr.to_str().expect("Failed to decode error message from Z3 as UTF-8").to_string()
    }
}

pub use goal::Goal;
pub use tactic::{ApplyResult,Tactic};
pub use probe::Probe;
pub use statistics::{Statistics, StatisticsValue};
