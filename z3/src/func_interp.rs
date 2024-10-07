use std::fmt;

use z3_sys::*;

use crate::{
    ast::Dynamic,
    HasContext, WrappedZ3, AstVector, FuncEntry,
    make_z3_object
};

make_z3_object! {
    /// Stores the interpretation of a function in a Z3 model.
    /// <https://z3prover.github.io/api/html/classz3py_1_1_func_interp.html>
    pub struct FuncInterp<'ctx>
    where
        sys_ty: Z3_func_interp,
        inc_ref: Z3_func_interp_inc_ref,
        dec_ref: Z3_func_interp_dec_ref,
    ;
}

impl<'ctx> FuncInterp<'ctx> {
    /// Returns the number of arguments in the function interpretation.
    pub fn get_arity(&self) -> u32 {
        self.check_error_pass(unsafe { Z3_func_interp_get_arity(**self.ctx(), **self) }).unwrap()
    }

    /// Returns the number of entries in the function interpretation.
    pub fn get_num_entries(&self) -> u32 {
        self.check_error_pass(unsafe { Z3_func_interp_get_num_entries(**self.ctx(), **self) }).unwrap()
    }

    /// Adds an entry to the function interpretation.
    pub fn add_entry(&self, args: &[&Dynamic<'ctx>], value: &Dynamic<'ctx>) {
        let v = AstVector::new(self.ctx());
        for a in args {
            v.push(a);
        }
        unsafe { Z3_func_interp_add_entry(**self.ctx(), **self, *v, **value) };
        self.check_error().unwrap();
    }

    /// Returns the entries of the function interpretation.
    pub fn get_entries(&self) -> Vec<FuncEntry> {
        (0..self.get_num_entries())
            .map(|i| unsafe {
                FuncEntry::wrap_check_error(
                    self.ctx(),
                    Z3_func_interp_get_entry(**self.ctx(), **self, i),
                )
            })
            .collect()
    }

    /// Returns the else value of the function interpretation.
    /// Returns None if the else value is not set by Z3.
    pub fn get_else(&self) -> Dynamic<'ctx> {
        unsafe {
            Dynamic::wrap_check_error(
                self.ctx(),
                Z3_func_interp_get_else(**self.ctx(), **self),
            )
        }
    }

    /// Sets the else value of the function interpretation.
    pub fn set_else(&self, ast: &Dynamic) {
        unsafe { Z3_func_interp_set_else(**self.ctx(), **self, **ast) }
        self.check_error().unwrap();
    }
}

impl<'ctx> fmt::Display for FuncInterp<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "[")?;
        self.get_entries().into_iter().try_for_each(|e| {
            let n = e.get_num_args();
            if n > 1 {
                write!(f, "[")?;
            };
            write!(
                f,
                "{}",
                e.get_args()
                    .into_iter()
                    .map(|a| format!("{:?}", a))
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
            if n > 1 {
                write!(f, "]")?;
            }
            write!(f, " -> {}, ", e.get_value())
        })?;
        write!(f, "else -> {}", self.get_else())?;
        write!(f, "]")
    }
}

impl<'ctx> fmt::Debug for FuncInterp<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "FuncInterp({self})")
    }
}
