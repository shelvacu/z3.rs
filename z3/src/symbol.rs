use std::ffi::{CString, CStr};
use std::ptr::NonNull;

use z3_sys::*;

use crate::{Context, HasContext};

/// Symbols are used to name several term and type constructors.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Symbol {
    Int(i32),
    String(String),
}

impl Symbol {
    pub fn as_z3_symbol(&self, ctx: &Context) -> NonNull<Z3_symbol> {
        match self {
            Symbol::Int(i) => ctx.check_error_ptr(unsafe { Z3_mk_int_symbol(**ctx, *i as ::std::os::raw::c_int) }).unwrap(),
            Symbol::String(s) => {
                let ss = CString::new(s.clone()).unwrap();
                let p = ss.as_ptr();
                ctx.check_error_ptr(unsafe { Z3_mk_string_symbol(**ctx, p) }).unwrap()
            }
        }
    }

    /// ### Safety
    ///
    /// zptr must be a valid pointer
    pub unsafe fn from_z3_symbol(ctx: &Context, zptr: NonNull<Z3_symbol>) -> Self {
        let symbol_kind = ctx.check_error_pass(Z3_get_symbol_kind(**ctx, zptr)).unwrap();
        match symbol_kind {
            SymbolKind::String => {
                let str = ctx.check_error_str(Z3_get_symbol_string(**ctx, zptr)).unwrap();
                Symbol::String(str)
            }
            SymbolKind::Int => {
                let i = ctx.check_error_pass(Z3_get_symbol_int(**ctx, zptr)).unwrap();
                Symbol::Int(i)
            }
        }
    }
}

impl From<i32> for Symbol {
    fn from(val: i32) -> Self {
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
