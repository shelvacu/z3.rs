use std::ffi::CString;
use std::fmt;
use std::result::Result;

use z3_sys::*;

use crate::{Context, HasContext, WrappedZ3, Goal, make_z3_object};

make_z3_object! {
    /// Function/predicate used to inspect a goal and collect information
    /// that may be used to decide which solver and/or preprocessing step
    /// will be used.
    ///
    /// Z3 provides a variety of probes, which can be queried via
    /// [`Probe::list_all()`].
    pub struct Probe<'ctx>
    where
        sys_ty: Z3_probe,
        inc_ref: Z3_probe_inc_ref,
        dec_ref: Z3_probe_dec_ref,
    ;
}

impl<'ctx> Probe<'ctx> {
    /// Iterate through the valid probe names.
    ///
    /// # Example
    ///
    /// ```
    /// # use z3::{Config, Context, Probe};
    ///
    /// let ctx = Context::default();
    /// let probes: Vec<_> = Probe::list_all(&ctx).collect();
    /// assert!(probes.contains(&"is-quasi-pb".to_string()));
    /// ```
    pub fn list_all(
        ctx: &'ctx Context,
    ) -> impl Iterator<Item = String> + 'ctx {
        (0..ctx.num_probes()).map(move |n| {
            ctx.get_probe_name(n)
        })
    }

    /// Return a string containing a description of the probe with
    /// the given `name`.
    pub fn describe(ctx: &'ctx Context, name: &str) -> String {
        let probe_name = CString::new(name).unwrap();
        ctx.check_error_str(unsafe { Z3_probe_get_descr(**ctx, probe_name.as_ptr()) }).unwrap()
    }

    /// Return a probe associated with the given `name`.
    ///
    /// # Example
    ///
    /// ```
    /// # use z3::{Config, Context, Probe};
    ///
    /// let ctx = Context::default();
    /// let probe = Probe::new(&ctx, "is-qfbv");
    /// ```
    pub fn new(ctx: &'ctx Context, name: &str) -> Probe<'ctx> {
        let probe_name = CString::new(name).unwrap();
        unsafe { Self::wrap_check_error(ctx, Z3_mk_probe(**ctx, probe_name.as_ptr())) }
    }

    /// Execute the probe over the goal.
    ///
    /// The probe always produce a double value. "Boolean" probes return
    /// `0.0` for `false`, and a value different from `0.0` for `true`.
    pub fn apply(&self, goal: &'ctx Goal) -> f64 {
        self.check_error_pass(unsafe { Z3_probe_apply(**self.ctx(), **self, **goal) }).unwrap()
    }

    /// Return a probe that always evaluates to val.
    /// ```
    /// # use z3::{Config, Context, Probe};
    ///
    /// let ctx = Context::default();
    /// let probe = Probe::constant(&ctx, 1.0);
    /// ```
    pub fn constant(ctx: &'ctx Context, val: f64) -> Probe<'ctx> {
        unsafe { Self::wrap_check_error(ctx, Z3_probe_const(**ctx, val)) }
    }

    /// Return a probe that evaluates to "true" when the value returned
    /// by `self` is less than the value returned by `p`.
    ///
    /// NOTE: For probes, "true" is any value different from 0.0.
    pub fn lt(&self, p: Probe) -> Probe<'ctx> {
        unsafe {
            Self::wrap_check_error(
                self.ctx(),
                Z3_probe_lt(**self.ctx(), **self, *p),
            )
        }
    }

    /// Return a probe that evaluates to "true" when the value returned
    /// by `self` is greater than the value returned by `p`.
    pub fn gt(&self, p: &Probe) -> Probe<'ctx> {
        unsafe {
            Self::wrap_check_error(
                self.ctx(),
                Z3_probe_gt(**self.ctx(), **self, **p),
            )
        }
    }

    /// Return a probe that evaluates to "true" when the value returned
    /// by `self` is less than or equal to the value returned by `p`.
    pub fn le(&self, p: &Probe) -> Probe<'ctx> {
        unsafe {
            Self::wrap_check_error(
                self.ctx(),
                Z3_probe_le(**self.ctx(), **self, **p),
            )
        }
    }

    /// Return a probe that evaluates to "true" when the value returned
    /// by `self` is greater than or equal to the value returned by `p`.
    pub fn ge(&self, p: &Probe) -> Probe<'ctx> {
        unsafe {
            Self::wrap_check_error(
                self.ctx(),
                Z3_probe_ge(**self.ctx(), **self, **p),
            )
        }
    }

    /// Return a probe that evaluates to "true" when the value returned
    /// by `self` is equal to the value returned by `p`.
    pub fn eq(&self, p: &Probe) -> Probe<'ctx> {
        unsafe {
            Self::wrap_check_error(
                self.ctx(),
                Z3_probe_eq(**self.ctx(), **self, **p),
            )
        }
    }

    /// Return a probe that evaluates to "true" when `self` and `p` evaluates to true.
    pub fn and(&self, p: &Probe) -> Probe<'ctx> {
        unsafe {
            Self::wrap_check_error(
                self.ctx(),
                Z3_probe_and(**self.ctx(), **self, **p),
            )
        }
    }

    /// Return a probe that evaluates to "true" when `p1` or `p2` evaluates to true.
    pub fn or(&self, p: &Probe) -> Probe<'ctx> {
        unsafe {
            Self::wrap_check_error(
                self.ctx(),
                Z3_probe_or(**self.ctx(), **self, **p),
            )
        }
    }

    /// Return a probe that evaluates to "true" when `p` does not evaluate to true.
    pub fn not(&self) -> Probe<'ctx> {
        unsafe { Self::wrap_check_error(self.ctx(), Z3_probe_not(**self.ctx(), **self)) }
    }

    /// Return a probe that evaluates to "true" when the value returned
    /// by `self` is not equal to the value returned by `p`.
    pub fn ne(&self, p: &Probe) -> Probe<'ctx> {
        self.eq(p).not()
    }
}

impl<'ctx> fmt::Debug for Probe<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "<z3.probe>")
    }
}
