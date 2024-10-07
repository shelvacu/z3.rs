use std::fmt;

use z3_sys::*;

use crate::{
    ast::Dynamic, HasContext, WrappedZ3,
    make_z3_object,
};

make_z3_object! {
    /// Store the value of the interpretation of a function in a particular point.
    /// <https://z3prover.github.io/api/html/classz3py_1_1_func_entry.html>
    pub struct FuncEntry<'ctx> 
    where
        sys_ty: Z3_func_entry,
        inc_ref: Z3_func_entry_inc_ref,
        dec_ref: Z3_func_entry_dec_ref,
    ;
}

impl<'ctx> FuncEntry<'ctx> {
    /// Returns the value of the function.
    pub fn get_value(&self) -> Dynamic<'ctx> {
        unsafe {
            Dynamic::wrap_check_error(
                self.ctx(),
                Z3_func_entry_get_value(**self.ctx(), **self),
            )
        }
    }

    /// Returns the number of arguments in the function entry.
    pub fn get_num_args(&self) -> u32 {
        self.check_error_pass(unsafe { Z3_func_entry_get_num_args(**self.ctx(), **self) }).unwrap()
    }

    /// Returns the arguments of the function entry.
    pub fn get_args(&self) -> Vec<Dynamic<'ctx>> {
        (0..self.get_num_args())
            .map(|i| unsafe {
                Dynamic::wrap_check_error(
                    self.ctx(),
                    Z3_func_entry_get_arg(**self.ctx(), **self, i),
                )
            })
            .collect()
    }
}

impl<'ctx> fmt::Display for FuncEntry<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "[")?;
        self.get_args()
            .into_iter()
            .try_for_each(|a| write!(f, "{a}, "))?;
        write!(f, "{}", self.get_value())?;
        write!(f, "]")
    }
}

impl<'ctx> fmt::Debug for FuncEntry<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "[")?;
        self.get_args()
            .into_iter()
            .try_for_each(|a| write!(f, "{a:?}, "))?;
        write!(f, "{:?}", self.get_value())?;
        write!(f, "]")
    }
}
