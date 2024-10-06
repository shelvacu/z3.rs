use std::convert::TryInto;
use std::ffi::CStr;
use std::fmt;
use std::ops::Deref;

use z3_sys::*;

use crate::{Context, Symbol, HasContext};
use crate::ast::{self, Ast, FuncDecl, Sort, make_ast_object, unop};

make_ast_object! {
    /// Recursive function declaration. Every function has an associated declaration.
    ///
    /// The declaration assigns a name, a return sort (i.e., type), and
    /// the sort (i.e., type) of each of its arguments. This is the function declaration type
    /// you should use if you want to add a definition to your function, recursive or not.
    ///
    /// This struct can dereference into a [`FuncDecl`] to access its methods.
    ///
    /// # See also:
    ///
    /// - [`RecFuncDecl::add_def`]
    pub struct RecFuncDecl<'ctx>;
}

impl<'ctx> RecFuncDecl<'ctx> {
    pub fn new<S: Into<Symbol>>(
        ctx: &'ctx Context,
        name: S,
        domain: &[&Sort<'ctx>],
        range: &Sort<'ctx>,
    ) -> Self {
        assert!(domain.iter().all(|s| s.ctx() == ctx));
        assert_eq!(ctx, range.ctx());

        let domain: Vec<_> = domain.iter().map(|s| ***s).collect();
        let sym = name.into().as_z3_symbol(ctx);
        unsafe {
            Self::wrap_check_error(
                ctx,
                Z3_mk_rec_func_decl(
                    **ctx,
                    sym,
                    domain.len().try_into().unwrap(),
                    domain.as_ptr(),
                    **range,
                ),
            )
        }
    }

    unop! {
        pub fn get_range(Z3_get_range) -> Sort<'ctx>;
    }

    /// Adds the body to a recursive function.
    ///
    /// ```
    /// # use z3::{Config, Context, RecFuncDecl, Solver, Sort, Symbol, ast::Int, SatResult};
    /// # use std::convert::TryInto;
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// let mut f = RecFuncDecl::new(
    ///     &ctx,
    ///     "f",
    ///     &[&Sort::int(&ctx)],
    ///     &Sort::int(&ctx));
    /// let n = Int::new_const(&ctx, "n");
    /// f.add_def(
    ///     &[&n],
    ///     &Int::add(&ctx, &[&n, &Int::from_i64(&ctx, 1)])
    /// );
    ///
    /// let f_of_n = &f.apply(&[&n.clone()]);
    ///
    /// let solver = Solver::new(&ctx);
    /// let forall: z3::ast::Bool = z3::ast::forall_const(
    ///         &ctx,
    ///         &[&n],
    ///         &[],
    ///         &n.lt(&f_of_n.as_int().unwrap())
    ///     ).try_into().unwrap();
    ///
    /// solver.assert(&forall);
    /// let res = solver.check();
    /// assert_eq!(res, SatResult::Sat);
    /// ```
    ///
    /// Note that `args` should have the types corresponding to the `domain` of the `RecFuncDecl`.
    pub fn add_def<T: Ast<'ctx>>(&self, args: &[T], body: impl Ast<'ctx>) {
        assert!(args.iter().all(|arg| arg.ctx() == body.ctx()));
        assert_eq!(self.ctx(), body.ctx());

        let mut args: Vec<_> = args.iter().map(|s| **s).collect();
        assert_eq!(body.sort(), self.get_range());
        unsafe {
            Z3_add_rec_def(
                **self.ctx(),
                **self,
                self.arity(),
                args.as_mut_ptr(),
                *body,
            );
        };
        self.check_error().unwrap();
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
    pub fn arity(&self) -> u32 {
        self.check_error_pass(unsafe { Z3_get_arity(**self.ctx(), **self)}).unwrap()
    }


    pub fn as_func_decl(&self) -> FuncDecl<'ctx> {
        unsafe { FuncDecl::wrap(self.ctx(), **self) }
    }
}
