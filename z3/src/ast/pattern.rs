use std::convert::TryInto;

use z3_sys::*;

use crate::{ast::Ast, Context, HasContext, WrappedZ3};

use super::make_ast_object;

make_ast_object! {
    /// A pattern for quantifier instantiation, used to guide quantifier instantiation.
    pub struct Pattern<'ctx>;
}


impl<'ctx> Pattern<'ctx> {
    /// Create a pattern for quantifier instantiation.
    ///
    /// Z3 uses pattern matching to instantiate quantifiers. If a
    /// pattern is not provided for a quantifier, then Z3 will
    /// automatically compute a set of patterns for it. However, for
    /// optimal performance, the user should provide the patterns.
    ///
    /// Patterns comprise a list of terms. The list should be
    /// non-empty.  If the list comprises of more than one term, it is
    /// a called a multi-pattern.
    ///
    /// In general, one can pass in a list of (multi-)patterns in the
    /// quantifier constructor.
    ///
    /// # See also:
    ///
    /// - `ast::forall_const()`
    /// - `ast::exists_const()`
    pub fn new<T: Ast<'ctx>>(ctx: &'ctx Context, terms: &[T]) -> Self {
        assert!(!terms.is_empty());
        assert!(terms.iter().all(|t| t.ctx() == ctx));

        let terms: Vec<_> = terms.iter().map(|t| **t).collect();
        unsafe { Pattern::wrap_check_error(ctx, Z3_mk_pattern(**ctx, terms.len().try_into().unwrap(), terms.as_ptr())) }
    }
}
