use std::ffi::{CStr, CString};

use z3_sys::*;

use crate::{Context, HasContext, WrappedZ3, Symbol, make_z3_object};

make_z3_object! {
    /// Parameter set used to configure many components (simplifiers, tactics, solvers, etc).
    pub struct Params<'ctx>
    where
        sys_ty: Z3_params,
        inc_ref: Z3_params_inc_ref,
        dec_ref: Z3_params_dec_ref,
        to_str: Z3_params_to_string,
    ;
}

impl<'ctx> Params<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Params<'ctx> {
        unsafe { Self::wrap_check_error(ctx, Z3_mk_params(**ctx)) }
    }

    pub fn set_symbol<K: Into<Symbol>, V: Into<Symbol>>(&mut self, k: K, v: V) {
        unsafe {
            Z3_params_set_symbol(
                **self.ctx(),
                **self,
                k.into().as_z3_symbol(self.ctx()),
                v.into().as_z3_symbol(self.ctx()),
            );
        };
    }

    pub fn set_bool<K: Into<Symbol>>(&mut self, k: K, v: bool) {
        unsafe {
            Z3_params_set_bool(
                **self.ctx(),
                **self,
                k.into().as_z3_symbol(self.ctx()),
                v,
            );
        };
    }

    pub fn set_f64<K: Into<Symbol>>(&mut self, k: K, v: f64) {
        unsafe {
            Z3_params_set_double(
                **self.ctx(),
                **self,
                k.into().as_z3_symbol(self.ctx()),
                v,
            );
        };
    }

    pub fn set_u32<K: Into<Symbol>>(&mut self, k: K, v: u32) {
        unsafe {
            Z3_params_set_uint(
                **self.ctx(),
                **self,
                k.into().as_z3_symbol(self.ctx()),
                v,
            );
        };
    }
}

/// Get a global (or module) parameter.
///
/// # See also
///
/// - [`set_global_param()`]
/// - [`reset_all_global_params()`]
pub fn get_global_param(k: &str) -> Option<String> {
    let ks = CString::new(k).unwrap();
    let mut ptr:*const std::ffi::c_char = std::ptr::null();
    if unsafe { Z3_global_param_get(ks.as_ptr(), &mut ptr as *mut *const std::ffi::c_char) } {
        let vs = unsafe { CStr::from_ptr(ptr) };
        vs.to_str().ok().map(|vs| vs.to_owned())
    } else {
        None
    }
}

/// Set a global (or module) parameter. This setting is shared by all Z3 contexts.
///
/// # See also
///
/// - [`get_global_param()`]
/// - [`reset_all_global_params()`]
pub fn set_global_param(k: &str, v: &str) {
    let ks = CString::new(k).unwrap();
    let vs = CString::new(v).unwrap();
    unsafe { Z3_global_param_set(ks.as_ptr(), vs.as_ptr()) };
}

/// Restore the value of all global (and module) parameters. This command will not affect already created objects (such as tactics and solvers).
///
/// # See also
///
/// - [`get_global_param()`]
/// - [`set_global_param()`]
pub fn reset_all_global_params() {
    unsafe { Z3_global_param_reset_all() };
}
