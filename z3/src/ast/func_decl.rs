use std::convert::{TryInto, TryFrom};

use z3_sys::*;

use crate::{Context, Symbol};
use crate::ast::{self, Sort, Dynamic};
use super::{make_ast_object, impl_from_try_into_dynamic, unop, binop, trinop, varop};

make_ast_object! {
    /// Function declaration. Every constant and function have an associated declaration.
    ///
    /// The declaration assigns a name, a sort (i.e., type), and for function
    /// the sort (i.e., type) of each of its arguments. Note that, in Z3,
    /// a constant is a function with 0 arguments.
    ///
    /// # See also:
    ///
    /// - [`RecFuncDecl`]
    pub struct FuncDecl<'ctx>;
}

impl_from_try_into_dynamic!(FuncDecl, as_func_decl);

impl<'ctx> FuncDecl<'ctx> {
    pub fn new<S: Into<Symbol>>(
        ctx: &'ctx Context,
        name: S,
        domain: &[&Sort<'ctx>],
        range: &Sort<'ctx>,
    ) -> Self {
        assert!(domain.iter().all(|s| s.ctx() == ctx));
        assert_eq!(ctx, range.ctx());

        let domain: Vec<_> = domain.iter().map(|s| *s).collect();
        let sym = name.into().as_z3_symbol(ctx);
        unsafe {
            Self::wrap_check_error(
                ctx,
                Z3_mk_func_decl(
                    *ctx,
                    sym,
                    domain.len().try_into().unwrap(),
                    domain.as_ptr(),
                    *range,
                ),
            )
        }
    }

    /// Return the number of arguments of a function declaration.
    ///
    /// If the function declaration is a constant, then the arity is `0`.
    ///
    /// ```
    /// # use z3::{Config, Context, FuncDecl, Solver, Sort, Symbol};
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// let f = FuncDecl::new(
    ///     &ctx,
    ///     "f",
    ///     &[&Sort::int(&ctx), &Sort::real(&ctx)],
    ///     &Sort::int(&ctx));
    /// assert_eq!(f.arity(), 2);
    /// ```
    pub fn arity(&self) -> usize {
        self.check_error_pass(unsafe { Z3_get_arity(*self.ctx(), *self)}).unwrap().try_into().unwrap()
    }

    /// Create a constant (if `args` has length 0) or function application (otherwise).
    ///
    /// Note that `args` should have the types corresponding to the `domain` of the `FuncDecl`.
    pub fn apply(&self, args: &[&dyn ast::Ast<'ctx>]) -> ast::Dynamic<'ctx> {
        assert!(args.iter().all(|s| s.get_ctx() == self.ctx()));

        let args: Vec<_> = args.iter().map(|a| *a).collect();

        unsafe {
            ast::Dynamic::wrap_check_error(self.ctx, {
                Z3_mk_app(
                    *self.ctx(),
                    *self,
                    args.len().try_into().unwrap(),
                    args.as_ptr(),
                )
            })
        }
    }

    /// Return the `DeclKind` of this `FuncDecl`.
    pub fn kind(&self) -> DeclKind {
        self.check_error_pass(unsafe { Z3_get_decl_kind(*self.ctx(), *self) }).unwrap()
    }

    /// Return the name of this `FuncDecl`.
    pub fn name(&self) -> Symbol {
        let symbol = self.check_error_ptr(unsafe { Z3_get_decl_name(*ctx, zptr) }).unwrap();
        unsafe { Symbol::from_z3_symbol(self.ctx(), symbol) }
    }

    unop! {
        pub fn range(Z3_get_range) -> Sort<'ctx>;
    }
}
