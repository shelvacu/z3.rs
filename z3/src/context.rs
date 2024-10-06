use log::debug;
use std::ffi::CString;
use std::ptr::NonNull;
use std::marker::PhantomData;

use z3_sys::*;

use crate::{Config, HasContext};

/// Manager of all other Z3 objects, global configuration options, etc.
///
/// An application may use multiple Z3 contexts. Objects created in one context
/// cannot be used in another one. However, several objects may be "translated" from
/// one context to another. It is not safe to access Z3 objects from multiple threads.
///
/// # Examples:
///
/// Creating a context with the default configuration:
///
/// ```
/// use z3::{Config, Context};
/// let cfg = Config::new();
/// let ctx = Context::new(&cfg);
/// ```
///
/// # See also:
///
/// - [`Config`]
/// - [`Context::new()`]
#[derive(PartialEq, Eq, Debug)]
pub struct Context {
    ptr: NonNull<Z3_context>,
    // Z3_context might hold references to strings in Config, don't let it drop before Z3_del_context
    cfg: Config,
}

impl<'a> HasContext<'a> for &'a Context {
    fn ctx(&self) -> &'a Context {
        *self
    }
}

impl std::default::Default for Context {
    fn default() -> Self {
        Self::new(Config::default())
    }
}

impl Context {
    pub fn new(cfg: Config) -> Context {
        let z3_cfg = unsafe { Z3_mk_config() };
        debug!("new config {:p}", z3_cfg);
        let z3_cfg:NonNull<Z3_config> = NonNull::new(z3_cfg).unwrap();
        for (k, v) in cfg.kvs.iter() {
            unsafe { Z3_set_param_value(z3_cfg, k.as_ptr(), v.as_ptr()) };
            // no error handling for this one
        }

        let p = NonNull::new(unsafe { Z3_mk_context_rc(z3_cfg) }).unwrap();
        debug!("new context {:p}", p);
        unsafe { Z3_set_error_handler(p, None) };
        Context {
            ptr: p,
            cfg,
        }
    }

    /// Interrupt a solver performing a satisfiability test, a tactic processing a goal, or simplify functions.
    pub fn interrupt(&self) {
        self.handle().interrupt();
    }

    /// Obtain a handle that can be used to interrupt computation from another thread.
    ///
    /// # See also:
    ///
    /// - [`ContextHandle`]
    /// - [`ContextHandle::interrupt()`]
    pub fn handle<'ctx>(&'ctx self) -> ContextHandle<'ctx> {
        unsafe { ContextHandle::new(**self) }
    }

    /// Update a global parameter.
    ///
    /// # See also
    ///
    /// - [`Context::update_bool_param_value()`]
    pub fn update_param_value(&mut self, k: &str, v: &str) {
        let ks = CString::new(k).unwrap();
        let vs = CString::new(v).unwrap();
        unsafe { Z3_update_param_value(**self, ks.as_ptr(), vs.as_ptr()) };
    }

    /// Update a global parameter.
    ///
    /// This is a helper function.
    ///
    /// # See also
    ///
    /// - [`Context::update_param_value()`]
    pub fn update_bool_param_value(&mut self, k: &str, v: bool) {
        self.update_param_value(k, if v { "true" } else { "false" });
    }

    pub fn num_tactics(&self) -> u32 {
        self.check_error_pass(unsafe { Z3_get_num_tactics(**self) }).unwrap()
    }

    pub fn get_tactic_name(&self, idx: u32) -> String {
        let p = self.check_error_pass(unsafe { Z3_get_tactic_name(**self, idx) }).unwrap();
        assert!(!p.is_null());
        unsafe { std::ffi::CStr::from_ptr(p) }.to_str().unwrap().to_string()
    }

    pub fn num_probes(&self) -> u32 {
        self.check_error_pass(unsafe { Z3_get_num_probes(**self) }).unwrap()
    }

    pub fn get_probe_name(&self, idx: u32) -> String {
        let p = self.check_error_pass(unsafe { Z3_get_probe_name(**self, idx) }).unwrap();
        assert!(!p.is_null());
        unsafe { std::ffi::CStr::from_ptr(p) }.to_str().unwrap().to_string()
    }   
}

/// Handle that can be used to interrupt a computation from another thread.
///
/// # See also:
///
/// - [`Context::interrupt()`]
/// - [`Context::handle()`]
/// - [`ContextHandle::interrupt()`]
#[derive(PartialEq, Eq, Debug)]
pub struct ContextHandle<'ctx> {
    ptr: NonNull<Z3_context>,
    _phantom: PhantomData<&'ctx Context>,
}

impl<'ctx> ContextHandle<'ctx> {
    /// Safety: ptr must have 'ctx lifetime
    unsafe fn new(ptr: NonNull<Z3_context>) -> Self {
        Self{
            ptr,
            _phantom: PhantomData,
        }
    }

    /// Interrupt a solver performing a satisfiability test, a tactic processing a goal, or simplify functions.
    pub fn interrupt(&self) {
        unsafe {
            Z3_interrupt(self.ptr);
        }
    }
}

unsafe impl<'ctx> Sync for ContextHandle<'ctx> {}
unsafe impl<'ctx> Send for ContextHandle<'ctx> {}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe { Z3_del_context(**self) };
    }
}

impl std::ops::Deref for Context {
    type Target = NonNull<Z3_context>;

    fn deref(&self) -> &NonNull<Z3_context> {
        &self.ptr
    }
}
