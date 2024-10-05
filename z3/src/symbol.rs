use std::ffi::CString;
use std::ptr::NonNull;

use z3_sys::*;

use crate::{Context, Symbol};

impl Symbol {
    pub fn as_z3_symbol(&self, ctx: &Context) -> NonNull<Z3_symbol> {
        match self {
            Symbol::Int(i) => ctx.check_error_ptr(unsafe { Z3_mk_int_symbol(*ctx, *i as ::std::os::raw::c_int) }).unwrap(),
            Symbol::String(s) => {
                let ss = CString::new(s.clone()).unwrap();
                let p = ss.as_ptr();
                ctx.check_error_ptr(unsafe { Z3_mk_string_symbol(ctx.z3_ctx, p) }).unwrap()
            }
        }
    }
}

impl From<u32> for Symbol {
    fn from(val: u32) -> Self {
        Symbol::Int(val)
    }
}

impl From<String> for Symbol {
    fn from(val: String) -> Self {
        Symbol::String(val)
    }
}

impl From<&str> for Symbol {
    fn from(val: &str) -> Self {
        Symbol::String(val.to_owned())
    }
}
