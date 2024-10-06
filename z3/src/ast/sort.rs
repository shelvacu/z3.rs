use std::convert::TryInto;
use std::fmt;
use std::ptr::NonNull;

use z3_sys::*;

use crate::{Context, HasContext, WrappedZ3, Symbol};
use crate::ast::FuncDecl;

use super::make_ast_object;

make_ast_object! {
    /// Sorts represent the various 'types' of [`Ast`s](ast::Ast).
    pub struct Sort<'ctx>;
}

impl<'ctx> Sort<'ctx> {
    pub fn uninterpreted(ctx: &'ctx Context, name: impl Into<Symbol>) -> Sort<'ctx> {
        let name = name.into();
        let sym = name.as_z3_symbol(ctx);
        unsafe {
            Self::wrap_check_error(
                ctx,
                Z3_mk_uninterpreted_sort(**ctx, sym),
            )
        }
    }

    pub fn bool(ctx: &'ctx Context) -> Sort<'ctx> {
        unsafe { Self::wrap_check_error(ctx, Z3_mk_bool_sort(**ctx)) }
    }

    pub fn int(ctx: &'ctx Context) -> Sort<'ctx> {
        unsafe { Self::wrap_check_error(ctx, Z3_mk_int_sort(**ctx)) }
    }

    pub fn real(ctx: &'ctx Context) -> Sort<'ctx> {
        unsafe { Self::wrap_check_error(ctx, Z3_mk_real_sort(**ctx)) }
    }

    pub fn float(ctx: &'ctx Context, ebits: u32, sbits: u32) -> Sort<'ctx> {
        unsafe { Self::wrap_check_error(ctx, Z3_mk_fpa_sort(**ctx, ebits, sbits)) }
    }

    pub fn float32(ctx: &'ctx Context) -> Sort<'ctx> {
        Self::float(ctx, 8, 24)
    }

    pub fn double(ctx: &'ctx Context) -> Sort<'ctx> {
        Self::float(ctx, 11, 53)
    }

    pub fn string(ctx: &'ctx Context) -> Sort<'ctx> {
        unsafe { Self::wrap_check_error(ctx, Z3_mk_string_sort(**ctx)) }
    }

    pub fn bitvector(ctx: &'ctx Context, sz: u32) -> Sort<'ctx> {
        unsafe { Self::wrap_check_error(ctx, Z3_mk_bv_sort(**ctx, sz as ::std::os::raw::c_uint)) }
    }

    pub fn array(ctx: &'ctx Context, domain: &Sort<'ctx>, range: &Sort<'ctx>) -> Sort<'ctx> {
        unsafe {
            Self::wrap_check_error(
                ctx,
                Z3_mk_array_sort(**ctx, **domain, **range),
            )
        }
    }

    pub fn set(ctx: &'ctx Context, elt: &Sort<'ctx>) -> Sort<'ctx> {
        unsafe { Self::wrap_check_error(ctx, Z3_mk_set_sort(**ctx, **elt)) }
    }

    /// Create an enumeration sort.
    ///
    /// Creates a Z3 enumeration sort with the given `name`.
    /// The enum variants will have the names in `enum_names`.
    /// Three things are returned:
    /// - the created `Sort`,
    /// - constants to create the variants,
    /// - and testers to check if a value is equal to a variant.
    ///
    /// # Examples
    /// ```
    /// # use z3::{Config, Context, SatResult, Solver, Sort, Symbol};
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// # let solver = Solver::new(&ctx);
    /// let (colors, color_consts, color_testers) = Sort::enumeration(
    ///     &ctx,
    ///     "Color".into(),
    ///     &[
    ///         "Red".into(),
    ///         "Green".into(),
    ///         "Blue".into(),
    ///     ],
    /// );
    ///
    /// let red_const = color_consts[0].apply(&[]);
    /// let red_tester = &color_testers[0];
    /// let eq = red_tester.apply(&[&red_const]);
    /// solver.assert(eq);
    ///
    /// assert_eq!(solver.check(), SatResult::Sat);
    /// let model = solver.get_model().unwrap();;
    ///
    /// assert!(model.eval(&eq, true).unwrap().as_bool().unwrap().as_bool().unwrap());
    /// ```
    pub fn enumeration<S: Into<Symbol>, const N: usize>(
        ctx: &'ctx Context,
        name: impl Into<Symbol>,
        enum_names: [S; N],
    ) -> (Sort<'ctx>, [FuncDecl<'ctx>; N], [FuncDecl<'ctx>; N]) {
        use std::mem::MaybeUninit;
        let name = name.into().as_z3_symbol(ctx);
        // let enum_names: Vec<_> = enum_names.into_iter().map(|s| NonNull::new(s.into().as_z3_symbol(ctx)).unwrap()).collect();
        let enum_names = enum_names.map(|s| s.into().as_z3_symbol(ctx));
        let mut consts_testers:[MaybeUninit<[NonNull<Z3_ast>; N]>; 2] = [MaybeUninit::uninit(); 2];
        // let mut  enum_consts:Vec<MaybeUninit<*mut Z3_ast>> = vec![MaybeUninit::uninit(); enum_count];
        // let mut enum_testers:Vec<MaybeUninit<*mut Z3_ast>> = vec![MaybeUninit::uninit(); enum_count];

        let sort = unsafe {
            Self::wrap_check_error(
                ctx,
                Z3_mk_enumeration_sort(
                    **ctx,
                    name,
                    N.try_into().unwrap(),
                    enum_names.as_ptr(),
                    consts_testers[0].as_mut_ptr().cast::<NonNull<Z3_ast>>(),
                    consts_testers[1].as_mut_ptr().cast::<NonNull<Z3_ast>>(),
                ),
            )
        };

        let enum_consts = unsafe { consts_testers[0].assume_init() };
        let enum_testers = unsafe { consts_testers[1].assume_init() };
        
        let make_func = |ast| unsafe { FuncDecl::wrap(ctx, ast) };
        let enum_consts = enum_consts.map(make_func);
        let enum_testers = enum_testers.map(make_func);

        (sort, enum_consts, enum_testers)
    }

    pub fn sort_kind(&self) -> SortKind {
        self.check_error_pass(unsafe { Z3_get_sort_kind(**self.ctx(), **self) }).unwrap()
    }

    /// Returns `Some(e)` where `e` is the number of exponent bits if the sort
    /// is a `FloatingPoint` and `None` otherwise.
    pub fn float_exponent_size(&self) -> Option<u32> {
        if self.sort_kind() != SortKind::FloatingPoint { return None; }
        self.check_error_pass(unsafe { Z3_fpa_get_ebits(**self.ctx(), **self) }).ok()
    }

    /// Returns `Some(s)` where `s` is the number of significand bits if the sort
    /// is a `FloatingPoint` and `None` otherwise.
    pub fn float_significand_size(&self) -> Option<u32> {
        if self.sort_kind() != SortKind::FloatingPoint { return None; }
        self.check_error_pass(unsafe { Z3_fpa_get_sbits(**self.ctx(), **self) }).ok()
    }

    /// Return if this Sort is for an `Array` or a `Set`.
    ///
    /// # Examples
    /// ```
    /// # use z3::{Config, Context, Sort, ast::Ast, ast::Int, ast::Bool};
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// let bool_sort = Sort::bool(&ctx);
    /// let int_sort = Sort::int(&ctx);
    /// let array_sort = Sort::array(&ctx, &int_sort, &bool_sort);
    /// let set_sort = Sort::set(&ctx, &int_sort);
    /// assert!(array_sort.is_array());
    /// assert!(set_sort.is_array());
    /// assert!(!int_sort.is_array());
    /// assert!(!bool_sort.is_array());
    /// ```
    pub fn is_array(&self) -> bool {
        self.sort_kind() == SortKind::Array
    }

    /// Return the `Sort` of the domain for `Array`s of this `Sort`.
    ///
    /// If this `Sort` is an `Array` or `Set`, it has a domain sort, so return it.
    /// If this is not an `Array` or `Set` `Sort`, return `None`.
    /// # Examples
    /// ```
    /// # use z3::{Config, Context, Sort, ast::Ast, ast::Int, ast::Bool};
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// let bool_sort = Sort::bool(&ctx);
    /// let int_sort = Sort::int(&ctx);
    /// let array_sort = Sort::array(&ctx, &int_sort, &bool_sort);
    /// let set_sort = Sort::set(&ctx, &int_sort);
    /// assert_eq!(array_sort.array_domain().unwrap(), int_sort);
    /// assert_eq!(set_sort.array_domain().unwrap(), int_sort);
    /// assert!(int_sort.array_domain().is_none());
    /// assert!(bool_sort.array_domain().is_none());
    /// ```
    pub fn array_domain(&self) -> Option<Sort<'ctx>> {
        if !self.is_array() { return None; }
        let domain_sort = unsafe{Z3_get_array_sort_domain(**self.ctx(), **self)};
        let domain_sort = self.check_error_ptr(domain_sort).ok()?;
        Some(unsafe{
            Self::wrap(self.ctx(), domain_sort)
        })
    }

    /// Return the `Sort` of the range for `Array`s of this `Sort`.
    ///
    /// If this `Sort` is an `Array` it has a range sort, so return it.
    /// If this `Sort` is a `Set`, it has an implied range sort of `Bool`.
    /// If this is not an `Array` or `Set` `Sort`, return `None`.
    /// # Examples
    /// ```
    /// # use z3::{Config, Context, Sort, ast::Ast, ast::Int, ast::Bool};
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// let bool_sort = Sort::bool(&ctx);
    /// let int_sort = Sort::int(&ctx);
    /// let array_sort = Sort::array(&ctx, &int_sort, &bool_sort);
    /// let set_sort = Sort::set(&ctx, &int_sort);
    /// assert_eq!(array_sort.array_range().unwrap(), bool_sort);
    /// assert_eq!(set_sort.array_range().unwrap(), bool_sort);
    /// assert!(int_sort.array_range().is_none());
    /// assert!(bool_sort.array_range().is_none());
    /// ```
    pub fn array_range(&self) -> Option<Sort<'ctx>> {
        if !self.is_array() { return None; }
        let range_sort = unsafe { Z3_get_array_sort_range(**self.ctx(), **self) };
        let range_sort = self.check_error_ptr(range_sort).ok()?;
        Some(unsafe{
            Self::wrap(self.ctx(), range_sort)
        })
    }
}

/// A struct to represent when two sorts are of different types.
#[derive(Debug)]
pub struct SortDiffers<'ctx> {
    pub left: Sort<'ctx>,
    pub right: Sort<'ctx>,
}

impl<'ctx> fmt::Display for SortDiffers<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "Can not compare nodes, Sort does not match.  Nodes contain types {:?} and {:?}",
            self.left, self.right
        )
    }
}
