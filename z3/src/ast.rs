//! Abstract syntax tree (AST).

use std::ops::Deref;
use std::borrow::Borrow;
use std::cmp::{Eq, PartialEq};
use std::convert::{TryFrom, TryInto};
use std::ffi::{CStr, CString};
use std::fmt;
use std::hash::Hash;
use std::ptr::NonNull;

pub use z3_sys::AstKind;
use z3_sys::*;

use crate::{error::*, Context, HasContext, Symbol};

use num::{bigint::BigInt, rational::BigRational};

mod func_decl;
mod rec_func_decl;
mod pattern;
mod sort;

pub use sort::{Sort, SortDiffers};
pub use func_decl::FuncDecl;
pub use pattern::Pattern;

/// A struct to represent when an ast is not a function application.
#[derive(Debug)]
pub struct IsNotApp {
    kind: AstKind,
}

macro_rules! make_ast_object {
    (
        $(#[$struct_meta:meta])*
        $v:vis struct $name:ident < 'ctx >
        ;
    ) => {
        $crate::make_z3_object!{
            $(#[$struct_meta])*
            $v struct $name<'ctx>
            where
                sys_ty: Z3_ast,
                inc_ref: Z3_inc_ref,
                dec_ref: Z3_dec_ref,
                to_str: Z3_ast_to_string,
            ;
        }

        impl<'ctx> $crate::ast::Ast<'ctx> for $name<'ctx> {
            unsafe fn wrap_generic(ctx: &'ctx $crate::Context, ast: ::std::ptr::NonNull<::z3_sys::Z3_ast>) -> Self {
                Self::wrap(ctx, ast)
            }
        }

        impl<'a, 'b> $crate::ast::Translateable<$name<'a>> for $name<'b> {}

        impl<'ctx> ::std::cmp::Eq for $name<'ctx> {}

        impl<'ctx> ::std::hash::Hash for $name<'ctx> {
            fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
                $crate::HasContext::check_error_pass(
                    self,
                    unsafe {
                        Z3_get_ast_hash(**self.ctx(), **self)
                    }
                ).unwrap().hash(state)
            }
        }
    }
}

pub(super) use make_ast_object;

make_ast_object! {
    /// [`Ast`] node representing any node
    pub struct Dynamic<'ctx>;
}

make_ast_object! {
    /// [`Ast`] node representing a boolean value.
    pub struct Bool<'ctx>;
}

make_ast_object! {
    /// [`Ast`] node representing a integer value.
    pub struct Int<'ctx>;
}

make_ast_object! {
    /// [`Ast`] node representing a real-number value.
    pub struct Real<'ctx>;
}

make_ast_object! {
    /// [`Ast`] node representing a float value.
    pub struct Float<'ctx>;
}

make_ast_object! {
    /// [`Ast`] node representing a string value.
    pub struct AstString<'ctx>;
}

make_ast_object! {
    /// [`Ast`] node representing a bitvector value.
    pub struct BV<'ctx>;
}

make_ast_object! {
    /// [`Ast`] node representing an array value.
    pub struct Array<'ctx>;
}

make_ast_object! {
    /// [`Ast`] node representing a set value.
    pub struct Set<'ctx>;
}

make_ast_object! {
    /// [`Ast`] node representing a datatype value.
    pub struct Datatype<'ctx>;
}

make_ast_object! {
    /// [`Ast`] node representing a regular expression.
    /// ```
    /// use z3::ast;
    /// use z3::{Config, Context, Solver, SatResult};
    ///
    /// let cfg = Config::new();
    /// let ctx = &Context::new(&cfg);
    /// let solver = Solver::new(&ctx);
    /// let s = ast::String::new_const(ctx, "s");
    ///
    /// // the regexp representing foo[a-c]*
    /// let a = ast::Regexp::concat(ctx, &[
    ///     &ast::Regexp::literal(ctx, "foo"),
    ///     &ast::Regexp::range(ctx, &'a', &'c').star()
    /// ]);
    /// // the regexp representing [a-z]+
    /// let b = ast::Regexp::range(ctx, &'a', &'z').plus();
    /// // intersection of a and b is non-empty
    /// let intersect = ast::Regexp::intersect(ctx, &[&a, &b]);
    /// solver.assert(&s.regex_matches(&intersect));
    /// assert!(solver.check() == SatResult::Sat);
    /// ```
    pub struct Regexp<'ctx>;
}

macro_rules! unop {
    (
        $(
            $( #[ $attr:meta ] )* $v:vis fn $f:ident ( $z3fn:ident ) -> $retty:ty ;
        )*
    ) => {
        $(
            $( #[ $attr ] )*
            $v fn $f(&self) -> $retty {
                unsafe {
                    <$retty>::wrap_check_error(self.ctx, {
                        $z3fn(self.ctx(), **self)
                    })
                }
            }
        )*
    };
}
pub(super) use unop;

macro_rules! binop {
    (
        $(
            $( #[ $attr:meta ] )* $v:vis fn $f:ident ( $z3fn:ident, a ) -> $retty:ty ;
        )*
    ) => {
        $(
            $( #[ $attr ] )*
            $v fn $f(&self, other: &Self) -> $retty {
                assert!(self.ctx == other.ctx);
                unsafe {
                    <$retty>::wrap_check_error(self.ctx, {
                        $z3fn(**self.ctx(), **self, other.z3_ast)
                    })
                }
            }
        )*
    };
}
pub(super) use binop;

macro_rules! trinop {
    (
        $(
            $( #[ $attr:meta ] )* $v:vis fn $f:ident ( $z3fn:ident, a, b ) -> $retty:ty ;
        )*
    ) => {
        $(
            $( #[ $attr ] )*
            $v fn $f(&self, a: &Self, b: &Self) -> $retty {
                assert!((self.ctx == a.ctx) && (a.ctx == b.ctx));
                unsafe {
                    <$retty>::wrap_check_error(self.ctx, {
                        $z3fn(**self.ctx(), **self, a.z3_ast, b.z3_ast)
                    })
                }
            }
        )*
    };
}
pub(super) use trinop;

macro_rules! varop {
    (
        $(
            $( #[ $attr:meta ] )* $v:vis fn $f:ident ( $z3fn:ident, ... ) -> $retty:ty ;
        )*
    ) => {
        $(
            $( #[ $attr ] )*
            $v fn $f(ctx: &'ctx Context, values: &[impl Borrow<Self>]) -> $retty {
                assert!(values.iter().all(|v| v.borrow().ctx() == ctx));
                let tmp: Vec<_> = values.iter().map(|x| *x.borrow()).collect();
                let len_u32 = tmp.len().try_into().unwrap();
                unsafe {
                    <$retty>::wrap_check_error(ctx, {
                        $z3fn(*ctx, len_u32, tmp.as_ptr())
                    })
                }
            }
        )*
    };
}
pub(super) use varop;

/// Abstract syntax tree (AST) nodes represent terms, constants, or expressions.
/// The `Ast` trait contains methods common to all AST subtypes.
pub trait Ast<'ctx>: fmt::Debug + HasContext<'ctx> + Deref<Target = NonNull<Z3_ast>> {
    /// Wrap a raw [`Z3_ast`]
    ///
    /// Does not do any error checking, in contrast to [`#wrap`]
    ///
    /// # Safety
    ///
    /// The `ast` must be a valid pointer to a [`Z3_ast`]
    unsafe fn wrap_generic(ctx: &'ctx Context, ast: NonNull<Z3_ast>) -> Self
    where
        Self: Sized;

    /// Compare this `Ast` with another `Ast`, and get a [`Bool`]
    /// representing the result.
    ///
    /// This operation works with all possible `Ast`s (int, real, BV, etc), but the two
    /// `Ast`s being compared must be the same type.
    //
    // Note that we can't use the binop! macro because of the `pub` keyword on it
    fn _eq(&self, other: &Self) -> Bool<'ctx>
    where
        Self: Sized,
    {
        self._safe_eq(other).unwrap()
    }

    /// Compare this `Ast` with another `Ast`, and get a Result.  Errors if the sort does not
    /// match for the two values.
    fn _safe_eq(&self, other: &Self) -> Result<Bool<'ctx>, SortDiffers<'ctx>>
    where
        Self: Sized,
    {
        assert_eq!(self.ctx(), other.ctx());

        let left_sort = self.get_sort();
        let right_sort = other.get_sort();
        if left_sort == right_sort {
            Ok(unsafe {
                Bool::wrap_check_error(self.ctx(), {
                    Z3_mk_eq(**self.ctx(), **self, *other)
                })
            })
        } else {
            Err(SortDiffers::new(left_sort, right_sort))
        }
    }

    varop!{
        /// Compare this `Ast` with a list of other `Ast`s, and get a [`Bool`]
        /// which is true only if all arguments (including Self) are pairwise distinct.
        ///
        /// This operation works with all possible `Ast`s (int, real, BV, etc), but the
        /// `Ast`s being compared must all be the same type.
        fn distinct(Z3_mk_distinct, ...) -> Bool<'ctx>;
    }

    unop!{
        /// Get the [`Sort`] of the `Ast`.
        fn sort(Z3_get_sort) -> Sort<'ctx>;

        /// Simplify the `Ast`. Returns a new `Ast` which is equivalent,
        /// but simplified using algebraic simplification rules, such as
        /// constant propagation.
        fn simplify(Z3_simplify) -> Self;
    }

    /// Performs substitution on the `Ast`. The slice `substitutions` contains a
    /// list of pairs with a "from" `Ast` that will be substituted by a "to" `Ast`.
    fn substitute<T: Ast<'ctx>>(&self, substitutions: &[(&T, &T)]) -> Self
    {
        let this_ast = **self;
        let num_exprs:std::os::raw::c_uint = substitutions.len().try_into().unwrap();
        let mut froms: Vec<_> = vec![];
        let mut tos: Vec<_> = vec![];

        for (from_ast, to_ast) in substitutions {
            froms.push(*from_ast);
            tos.push(*to_ast);
        }
        unsafe {
            Self::wrap(self.ctx(), {
                Z3_substitute(
                    **self.ctx(),
                    this_ast,
                    num_exprs,
                    froms.as_ptr(),
                    tos.as_ptr(),
                )
            })
        }
    }

    /// Return the number of children of this `Ast`.
    ///
    /// Leaf nodes (eg `Bool` consts) will return 0.
    fn num_children(&self) -> usize {
        let res = unsafe {
            Z3_get_app_num_args(**self.ctx(), **self)
        };
        self.check_error().unwrap();
        res.try_into().unwrap()
    }

    /// Return the `n`th child of this `Ast`.
    ///
    /// Out-of-bound indices will return `None`.
    fn nth_child(&self, idx: usize) -> Option<Dynamic<'ctx>> {
        if idx >= self.num_children() {
            return None;
        }
        let idx = u32::try_from(idx).unwrap();
        let child_ast = unsafe {
            Z3_get_app_arg(**self.ctx(), **self, idx)
        };
        Some(unsafe { Dynamic::wrap_check_error(self.ctx(), child_ast) })
    }

    /// Return the children of this node as a `Vec<Dynamic>`.
    fn children(&self) -> Vec<Dynamic<'ctx>> {
        let n = self.num_children();
        (0..n).map(|i| self.nth_child(i).unwrap()).collect()
    }

    /// Return the `AstKind` for this `Ast`.
    fn kind(&self) -> AstKind {
        let res = unsafe {
            Z3_get_ast_kind(**self.ctx(), **self)
        };
        check_error(self.ctx()).unwrap();
        res
    }

    /// Return `true` if this is a Z3 function application.
    ///
    /// Note that constants are function applications with 0 arguments.
    fn is_app(&self) -> bool {
        let kind = self.kind();
        kind == AstKind::Numeral || kind == AstKind::App
    }

    /// Return `true` if this is a Z3 constant.
    ///
    /// Note that constants are function applications with 0 arguments.
    fn is_const(&self) -> bool {
        self.is_app() && self.num_children() == 0
    }

    /// Return the `FuncDecl` of the `Ast`.
    ///
    /// This will panic if the `Ast` is not an app, i.e. if [`AstKind`] is not
    /// [`AstKind::App`] or [`AstKind::Numeral`].
    fn decl(&self) -> FuncDecl<'ctx> {
        self.safe_decl().expect("Ast is not an app")
    }

    fn safe_decl(&self) -> Result<FuncDecl<'ctx>, IsNotApp> {
        if !self.is_app() {
            Err(IsNotApp::new(self.kind()))
        } else {
            let func_decl = unsafe {
                Z3_get_app_decl(**self.ctx(), **self)
            };
            Ok(unsafe { FuncDecl::wrap_check_error(self.ctx(), func_decl) })
        }
    }
}

/// One Ast type is translateable to another Ast type iff:
///   - they're the same type other than the 'ctx lifetime OR
///   - Self is dynamic (doesn't care about the underlying Z3_ast_kind)
trait Translateable<F> {}

pub trait AstTranslate<'f_ctx, 't_ctx, F>
where
    F: Ast<'f_ctx>,
    Self: Ast<'t_ctx> + Translateable<F>,
{
    fn translate(from: &F, dest: &'t_ctx Context) -> Self;
}

impl<'f_ctx,'t_ctx,F,T> AstTranslate<'f_ctx,'t_ctx,F> for T
where
    T: Translateable<F>,
    F: Ast<'f_ctx>,
    T: Ast<'t_ctx>,
{
    fn translate(from: &F, dest: &'t_ctx Context) -> T {
        if from.ctx() == dest {
            panic!("Cannot translate from one context to the same context");
        }
        unsafe {
            T::wrap(dest, Z3_translate(from.ctx().z3_ctx, *from, dest.z3_ctx))
        }
    }
}

impl<'ctx, T, U> PartialEq<U> for T
where
    T: Ast<'ctx>,
    U: Ast<'ctx>,
{
    fn eq(&self, other: &U) -> bool {
        self.check_error_pass(unsafe { Z3_is_eq_ast(**self.ctx(), **self, *other) })
    }
}

macro_rules! impl_from_try_into_dynamic {
    ($ast:ident, $as_ast:ident) => {
        impl<'ctx> From<$ast<'ctx>> for Dynamic<'ctx> {
            fn from(ast: $ast<'ctx>) -> Self {
                Dynamic::from_ast(ast)
            }
        }

        impl<'ctx> TryFrom<Dynamic<'ctx>> for $ast<'ctx> {
            type Error = std::string::String;
            fn try_from(ast: Dynamic<'ctx>) -> Result<Self, std::string::String> {
                ast.$as_ast()
                    .ok_or_else(|| format!("Dynamic is not of requested type: {:?}", ast))
            }
        }
    };
}
pub(super) use impl_from_try_into_dynamic;

impl_from_try_into_dynamic!(Bool, as_bool);
impl_from_try_into_dynamic!(Int, as_int);
impl_from_try_into_dynamic!(Real, as_real);
impl_from_try_into_dynamic!(Float, as_float);
impl_from_try_into_dynamic!(StringAst, as_string);
impl_from_try_into_dynamic!(BV, as_bv);
impl_from_try_into_dynamic!(Array, as_array);
impl_from_try_into_dynamic!(Set, as_set);

impl<'ctx> Int<'ctx> {
    pub fn from_big_int(ctx: &'ctx Context, value: &BigInt) -> Int<'ctx> {
        Int::from_str(ctx, &value.to_str_radix(10)).unwrap()
    }

    pub fn from_str(ctx: &'ctx Context, value: &str) -> Option<Int<'ctx>> {
        let sort = Sort::int(ctx);
        let int_cstring = CString::new(value).unwrap();
        let ast = self.check_error_ptr(unsafe {
            Z3_mk_numeral(*ctx, int_cstring.as_ptr(), *sort)
        }).ok()?;
        Some(unsafe { Int::wrap(ctx, ast) })
    }
}

impl<'ctx> Real<'ctx> {
    pub fn from_big_rational(ctx: &'ctx Context, value: &BigRational) -> Real<'ctx> {
        let num = value.numer();
        let den = value.denom();
        Real::from_real_str(ctx, &num.to_str_radix(10), &den.to_str_radix(10)).unwrap()
    }

    pub fn from_real_str(ctx: &'ctx Context, num: &str, den: &str) -> Option<Real<'ctx>> {
        let sort = Sort::real(ctx);
        let fraction_cstring = CString::new(format!("{num:} / {den:}")).unwrap();
        let ast = self.check_error_ptr(unsafe { Z3_mk_numeral(*ctx, fraction_cstring.as_ptr(), *sort) }).ok()?;
        Some(unsafe { Real::wrap(ctx, ast) })
    }
}

impl<'ctx> Float<'ctx> {
    // Create a 32-bit (IEEE-754) Float [`Ast`] from a rust f32
    pub fn from_f32(ctx: &'ctx Context, value: f32) -> Float<'ctx> {
        let sort = Sort::float32(ctx);
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_fpa_numeral_float(*ctx, value, *sort)
            })
        }
    }

    // Create a 364-bit (IEEE-754) Float [`Ast`] from a rust f64
    pub fn from_f64(ctx: &'ctx Context, value: f64) -> Float<'ctx> {
        let sort = Sort::double(ctx);
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_fpa_numeral_double(*ctx, value, *sort)
            })
        }
    }

    pub fn as_f64(&self) -> f64 {
        let res = unsafe { Z3_get_numeral_double(**self.ctx(), **self) };
        self.check_error().unwrap();
        res
    }
}

impl_from_try_into_dynamic!(Datatype, as_datatype);

impl<'ctx> Bool<'ctx> {
    pub fn new_const<S: Into<Symbol>>(ctx: &'ctx Context, name: S) -> Bool<'ctx> {
        let sort = Sort::bool(ctx);
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_const(*ctx, name.into().as_z3_symbol(ctx), *sort)
            })
        }
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str) -> Bool<'ctx> {
        let sort = Sort::bool(ctx);
        let pp = CString::new(prefix).unwrap();
        let p = pp.as_ptr();
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_fresh_const(*ctx, p, *sort)
            })
        }
    }

    pub fn from_bool(ctx: &'ctx Context, b: bool) -> Bool<'ctx> {
        unsafe {
            Self::wrap_check_error(ctx, {
                if b {
                    Z3_mk_true(*ctx)
                } else {
                    Z3_mk_false(*ctx)
                }
            })
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        unsafe {
            match self.check_error_pass(Z3_get_bool_value(**self.ctx(), **self)).unwrap() {
                Z3_L_TRUE => Some(true),
                Z3_L_FALSE => Some(false),
                _ => None,
            }
        }
    }

    // This doesn't quite fit the trinop! macro because of the generic argty
    pub fn ite<T>(&self, a: &T, b: &T) -> T
    where
        T: Ast<'ctx>,
    {
        unsafe {
            T::wrap_check_error(self.ctx, {
                Z3_mk_ite(**self.ctx(), **self, *a, *b)
            })
        }
    }

    varop! {
        pub fn and(Z3_mk_and, ...) -> Self;
        pub fn or(Z3_mk_or, ...) -> Self;
    }
    binop! {
        pub fn xor(Z3_mk_xor, a) -> Self;
        pub fn iff(Z3_mk_iff, a) -> Self;
        pub fn implies(Z3_mk_implies, a) -> Self;
    }
    unop! {
        pub fn not(Z3_mk_not) -> Self;
    }

    pub fn pb_le(ctx: &'ctx Context, values: &[(&Bool<'ctx>, i32)], k: i32) -> Bool<'ctx> {
        let len_u32:u32 = values.len().try_into().unwrap();
        let (values, coefficients): (Vec<Z3_ast>, Vec<i32>) = values
            .iter()
            .map(|(boolean, coefficient)| (*boolean, coefficient))
            .unzip();
        unsafe {
            Bool::wrap_check_error(ctx,
                Z3_mk_pble(
                    *ctx,
                    len_u32,
                    values.as_ptr(),
                    coefficients.as_ptr(),
                    k,
                )
            )
        }
    }
    pub fn pb_ge(ctx: &'ctx Context, values: &[(&Bool<'ctx>, i32)], k: i32) -> Bool<'ctx> {
        let len_u32:u32 = values.len().try_into().unwrap();
        let (values, coefficients): (Vec<Z3_ast>, Vec<i32>) = values
            .iter()
            .map(|(boolean, coefficient)| (*boolean, coefficient))
            .unzip();
        unsafe {
            Bool::wrap_check_error(ctx,
                Z3_mk_pbge(
                    *ctx,
                    len_u32,
                    values.as_ptr(),
                    coefficients.as_ptr(),
                    k,
                )
            )
        }
    }
    pub fn pb_eq(ctx: &'ctx Context, values: &[(&Bool<'ctx>, i32)], k: i32) -> Bool<'ctx> {
        let len_u32:u32 = values.len().try_into().unwrap();
        let (values, coefficients): (Vec<Z3_ast>, Vec<i32>) = values
            .iter()
            .map(|(boolean, coefficient)| (*boolean, coefficient))
            .unzip();
        unsafe {
            Bool::wrap_check_error(ctx,
                Z3_mk_pbeq(
                    *ctx,
                    len_u32,
                    values.as_ptr(),
                    coefficients.as_ptr(),
                    k,
                )
            )
        }
    }
}

impl<'ctx> Int<'ctx> {
    pub fn new_const<S: Into<Symbol>>(ctx: &'ctx Context, name: S) -> Int<'ctx> {
        let sort = Sort::int(ctx);
        let sym = name.into().as_z3_symbol(ctx);
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_const(*ctx, sym, *sort)
            })
        }
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str) -> Int<'ctx> {
        let sort = Sort::int(ctx);
        let pp = CString::new(prefix).unwrap();
        let p = pp.as_ptr();
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_fresh_const(*ctx, p, *sort)
            })
        }
    }

    pub fn from_i64(ctx: &'ctx Context, i: i64) -> Int<'ctx> {
        let sort = Sort::int(ctx);
        unsafe { Self::wrap_check_error(ctx, Z3_mk_int64(*ctx, i, *sort)) }
    }

    pub fn from_u64(ctx: &'ctx Context, u: u64) -> Int<'ctx> {
        let sort = Sort::int(ctx);
        unsafe { Self::wrap_check_error(ctx, Z3_mk_unsigned_int64(*ctx, u, *sort)) }
    }

    pub fn as_i64(&self) -> Option<i64> {
        let mut tmp:i64 = 0;
        let res = check_error_pass(
            unsafe {
                Z3_get_numeral_int64(**self.ctx(), **self, &mut tmp)
            }
        ).unwrap();
        if res {
            Some(tmp)
        } else {
            None
        }
    }

    pub fn as_u64(&self) -> Option<u64> {
        let mut tmp:u64 = 0;
        let res = check_error_pass(
            unsafe {
                Z3_get_numeral_uint64(**self.ctx(), **self, &mut tmp)
            }
        ).unwrap();
        if res {
            Some(tmp)
        } else {
            None
        }
    }

    pub fn from_real(ast: &Real<'ctx>) -> Int<'ctx> {
        unsafe { Self::wrap_check_error(ast.ctx, Z3_mk_real2int(*ast.ctx(), *ast)) }
    }

    /// Create a real from an integer.
    /// This is just a convenience wrapper around
    /// [`Real::from_int()`]; see notes there.
    pub fn to_real(&self) -> Real<'ctx> {
        Real::from_int(self)
    }

    /// Create an integer from a bitvector.
    ///
    /// Signed and unsigned version.
    ///
    /// # Examples
    /// ```
    /// # use z3::{ast, Config, Context, SatResult, Solver};
    /// # use z3::ast::Ast;
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// # let solver = Solver::new(&ctx);
    /// let bv = ast::BV::new_const(&ctx, "x", 32);
    /// solver.assert(&bv._eq(&ast::BV::from_i64(&ctx, -3, 32)));
    ///
    /// let x = ast::Int::from_bv(&bv, true);
    ///
    /// assert_eq!(solver.check(), SatResult::Sat);
    /// let model = solver.get_model().unwrap();
    ///
    /// assert_eq!(-3, model.eval(&x, true).unwrap().as_i64().unwrap());
    /// ```
    pub fn from_bv(ast: &BV<'ctx>, signed: bool) -> Int<'ctx> {
        unsafe {
            Self::wrap_check_error(ast.ctx, {
                Z3_mk_bv2int(*ast.ctx(), *ast, signed)
            })
        }
    }

    /// Create a bitvector from an integer.
    /// This is just a convenience wrapper around
    /// [`BV::from_int()`]; see notes there.
    pub fn to_ast(&self, sz: u32) -> BV<'ctx> {
        BV::from_int(self, sz)
    }

    varop! {
        pub fn add(Z3_mk_add, ...) -> Self;
        pub fn sub(Z3_mk_sub, ...) -> Self;
        pub fn mul(Z3_mk_mul, ...) -> Self;
    }
    unop! {
        pub fn unary_minus(Z3_mk_unary_minus) -> Self;
    }
    binop! {
        pub fn div(Z3_mk_div, a) -> Self;
        pub fn rem(Z3_mk_rem, a) -> Self;
        pub fn modulo(Z3_mk_mod, a) -> Self;
        pub fn power(Z3_mk_power, a) -> Real<'ctx>;
        pub fn lt(Z3_mk_lt, a) -> Bool<'ctx>;
        pub fn le(Z3_mk_le, a) -> Bool<'ctx>;
        pub fn gt(Z3_mk_gt, a) -> Bool<'ctx>;
        pub fn ge(Z3_mk_ge, a) -> Bool<'ctx>;
    }
    // Z3 does support mixing ints and reals in add(), sub(), mul(), div(), and power()
    //   (but not rem(), modulo(), lt(), le(), gt(), or ge()).
    // TODO: we could consider expressing this by having a Numeric trait with these methods.
    //    Int and Real would have the Numeric trait, but not the other Asts.
    // For example:
    //   fn add(&self, other: &impl Numeric<'ctx>) -> Dynamic<'ctx> { ... }
    // Note the return type would have to be Dynamic I think (?), as the exact result type
    //   depends on the particular types of the inputs.
    // Alternately, we could just have
    //   Int::add_real(&self, other: &Real<'ctx>) -> Real<'ctx>
    // and
    //   Real::add_int(&self, other: &Int<'ctx>) -> Real<'ctx>
    // This might be cleaner because we know exactly what the output type will be for these methods.
}

impl<'ctx> Real<'ctx> {
    pub fn new_const<S: Into<Symbol>>(ctx: &'ctx Context, name: S) -> Real<'ctx> {
        let sort = Sort::real(ctx);
        let name_sym = name.into().as_z3_symbol(ctx);
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_const(*ctx, name_sym, *sort)
            })
        }
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str) -> Real<'ctx> {
        let sort = Sort::real(ctx);
        let pp = CString::new(prefix).unwrap();
        let p = pp.as_ptr();
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_fresh_const(*ctx, p, *sort)
            })
        }
    }

    pub fn from_real(ctx: &'ctx Context, num: i32, den: i32) -> Real<'ctx> {
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_real(
                    *ctx,
                    num as ::std::os::raw::c_int,
                    den as ::std::os::raw::c_int,
                )
            })
        }
    }

    pub fn as_real(&self) -> Option<(i64, i64)> {
        let mut num: i64 = 0;
        let mut den: i64 = 0;
        unsafe { Z3_get_numeral_small(**self.ctx(), **self, &mut num, &mut den) };
        self.check_error().ok().map(|()| (num, den))
    }

    pub fn approx(&self, precision: usize) -> ::std::string::String {
        let precision_convert = precision.try_into().unwrap();
        let zstr = self.check_error_ptr(
            unsafe {
                Z3_get_numeral_decimal_string(
                    **self.ctx(),
                    **self,
                    precision_convert,
                )
            }
        ).unwrap();
        let s = unsafe { CStr::from_ptr(zstr) }
            .to_str()
            .unwrap();
        s.strip_suffix('?').unwrap_or(s).to_owned()
    }

    pub fn approx_f64(&self) -> f64 {
        self.approx(17).parse().unwrap() // 17 decimal digits needed to get full f64 precision
    }

    pub fn from_int(ast: &Int<'ctx>) -> Real<'ctx> {
        unsafe { Self::wrap_check_error(ast.ctx, Z3_mk_int2real(*ast.ctx(), *ast)) }
    }

    /// Create an integer from a real.
    /// This is just a convenience wrapper around
    /// [`Int::from_real()`]; see notes there.
    pub fn to_int(&self) -> Int<'ctx> {
        Int::from_real(self)
    }

    unop! {
        pub fn is_int(Z3_mk_is_int) -> Bool<'ctx>;
        pub fn unary_minus(Z3_mk_unary_minus) -> Self;
    }

    varop! {
        pub fn add(Z3_mk_add, ...) -> Self;
        pub fn sub(Z3_mk_sub, ...) -> Self;
        pub fn mul(Z3_mk_mul, ...) -> Self;
    }

    binop! {
        pub fn div(Z3_mk_div, a) -> Self;
        pub fn power(Z3_mk_power, a) -> Self;
        pub fn lt(Z3_mk_lt, a) -> Bool<'ctx>;
        pub fn le(Z3_mk_le, a) -> Bool<'ctx>;
        pub fn gt(Z3_mk_gt, a) -> Bool<'ctx>;
        pub fn ge(Z3_mk_ge, a) -> Bool<'ctx>;
    }
}

impl<'ctx> Float<'ctx> {
    pub fn new_const<S: Into<Symbol>>(
        ctx: &'ctx Context,
        name: S,
        ebits: u32,
        sbits: u32,
    ) -> Float<'ctx> {
        let sort = Sort::float(ctx, ebits, sbits);
        let name_sym = name.into().as_z3_symbol(ctx);
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_const(*ctx, name_sym, *sort)
            })
        }
    }

    /// Create a 32-bit (IEEE-754) Float [`Ast`].
    pub fn new_const_float32<S: Into<Symbol>>(ctx: &'ctx Context, name: S) -> Float<'ctx> {
        let sort = Sort::float32(ctx);
        let name_sym = name.into().as_z3_symbol(ctx);
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_const(*ctx, name_sym, *sort)
            })
        }
    }

    /// Create a 64-bit (IEEE-754) Float [`Ast`].
    pub fn new_const_double<S: Into<Symbol>>(ctx: &'ctx Context, name: S) -> Float<'ctx> {
        let sort = Sort::double(ctx);
        let name_sym = name.into().as_z3_symbol(ctx);
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_const(*ctx, name_sym, *sort)
            })
        }
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str, ebits: u32, sbits: u32) -> Float<'ctx> {
        let sort = Sort::float(ctx, ebits, sbits);
        let pp = CString::new(prefix).unwrap();
        let p = pp.as_ptr();
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_fresh_const(*ctx, p, *sort)
            })
        }
    }

    pub fn fresh_const_float32(ctx: &'ctx Context, prefix: &str) -> Float<'ctx> {
        let sort = Sort::float32(ctx);
        let pp = CString::new(prefix).unwrap();
        let p = pp.as_ptr();
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_fresh_const(*ctx, p, *sort)
            })
        }
    }

    pub fn fresh_const_double(ctx: &'ctx Context, prefix: &str) -> Float<'ctx> {
        let sort = Sort::double(ctx);
        let pp = CString::new(prefix).unwrap();
        let p = pp.as_ptr();
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_fresh_const(*ctx, p, *sort)
            })
        }
    }

    // Add two floats of the same size, rounding towards zero
    pub fn add_towards_zero(&self, other: &Self) -> Float<'ctx> {
        Self::round_towards_zero(self.ctx).add(self, other)
    }

    // Subtract two floats of the same size, rounding towards zero
    pub fn sub_towards_zero(&self, other: &Self) -> Float<'ctx> {
        Self::round_towards_zero(self.ctx).sub(self, other)
    }

    // Multiply two floats of the same size, rounding towards zero
    pub fn mul_towards_zero(&self, other: &Self) -> Float<'ctx> {
        Self::round_towards_zero(self.ctx).mul(self, other)
    }

    // Divide two floats of the same size, rounding towards zero
    pub fn div_towards_zero(&self, other: &Self) -> Float<'ctx> {
        Self::round_towards_zero(self.ctx).div(self, other)
    }

    unop! {
        pub fn round_towards_zero(Z3_mk_fpa_round_toward_zero) -> Float<'ctx>;
        pub fn round_towards_negative(Z3_mk_fpa_round_toward_negative) -> Float<'ctx>;
        pub fn round_towards_positive(Z3_mk_fpa_round_toward_positive) -> Float<'ctx>;
        pub fn unary_abs(Z3_mk_fpa_abs) -> Self;
        pub fn unary_neg(Z3_mk_fpa_neg) -> Self;
    }
    binop! {
        pub fn lt(Z3_mk_fpa_lt, a) -> Bool<'ctx>;
        pub fn le(Z3_mk_fpa_leq, a) -> Bool<'ctx>;
        pub fn gt(Z3_mk_fpa_gt, a) -> Bool<'ctx>;
        pub fn ge(Z3_mk_fpa_geq, a) -> Bool<'ctx>;
    }
    trinop! {
        pub fn add(Z3_mk_fpa_add, a, b) -> Self;
        pub fn sub(Z3_mk_fpa_sub, a, b) -> Self;
        pub fn mul(Z3_mk_fpa_mul, a, b) -> Self;
        pub fn div(Z3_mk_fpa_div, a, b) -> Self;
    }
}

impl<'ctx> AstString<'ctx> {
    /// Creates a new constant using the built-in string sort
    pub fn new_const<S: Into<Symbol>>(ctx: &'ctx Context, name: S) -> String<'ctx> {
        let sort = Sort::string(ctx);
        let name_sym = name.into().as_z3_symbol(ctx);
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_const(*ctx, name_sym, *sort)
            })
        }
    }

    /// Creates a fresh constant using the built-in string sort
    pub fn fresh_const(ctx: &'ctx Context, prefix: &str) -> String<'ctx> {
        let sort = Sort::string(ctx);
        let pp = CString::new(prefix).unwrap();
        let p = pp.as_ptr();
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_fresh_const(*ctx, p, *sort)
            })
        }
    }

    /// Creates a Z3 constant string from a `&str`
    pub fn from_str(ctx: &'ctx Context, string: &str) -> Result<String<'ctx>, std::ffi::NulError> {
        let string = CString::new(string)?;
        let ptr = string.as_c_str().as_ptr();
        Ok(unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_string(*ctx, ptr)
            })
        })
    }

    /// Retrieves the underlying `std::string::String`
    ///
    /// If this is not a constant `z3::ast::String`, return `None`.
    ///
    /// Note that `to_string()` provided by `std::string::ToString` (which uses
    /// `std::fmt::Display`) returns an escaped string. In contrast,
    /// `z3::ast::String::from_str(&ctx, s).unwrap().as_string()` returns a
    /// `String` equal to the original value.
    pub fn as_string(&self) -> Option<std::string::String> {
        let z3_ctx = **self.ctx();
        let zstr = self.check_error_ptr(
            unsafe {
                Z3_get_string(z3_ctx, **self)
            }
        ).ok()?;
        Some(unsafe { CStr::from_ptr(zstr) }
            .to_string_lossy()
            .into_owned())
    }

    /// Checks if this string matches a `z3::ast::Regexp`
    pub fn regex_matches(&self, regex: &Regexp) -> Bool<'ctx> {
        assert!(self.ctx == regex.ctx);
        unsafe {
            Bool::wrap_check_error(
                self.ctx,
                Z3_mk_seq_in_re(**self.ctx(), **self, *regex),
            )
        }
    }

    varop! {
        /// Appends the argument strings to `Self`
        pub fn concat(Z3_mk_seq_concat, ...) -> String<'ctx>;
    }

    binop! {
        /// Checks whether `Self` contains a substring
        pub fn contains(Z3_mk_seq_contains, a) -> Bool<'ctx>;
        /// Checks whether `Self` is a prefix of the argument
        pub fn prefix(Z3_mk_seq_prefix, a) -> Bool<'ctx>;
        /// Checks whether `Self` is a suffix of the argument
        pub fn suffix(Z3_mk_seq_suffix, a) -> Bool<'ctx>;
    }
}

macro_rules! bv_overflow_check_signed {
    (
        $(
            $( #[ $attr:meta ] )* $v:vis fn $f:ident ( $z3fn:ident ) ;
        )*
    ) => {
        $(
            $( #[ $attr ] )*
            $v fn $f(&self, other: &BV<'ctx>, b: bool) -> Bool<'ctx> {
                unsafe {
                    Ast::wrap_check_error(self.ctx, {
                        $z3fn(**self.ctx(), **self, other.z3_ast, b)
                    })
                }
            }
        )*
    };
}

impl<'ctx> BV<'ctx> {
    pub fn from_str(ctx: &'ctx Context, sz: u32, value: &str) -> Result<BV<'ctx>, Error> {
        let sort = Sort::bitvector(ctx, sz);
        let bv_cstring = CString::new(value).unwrap();
        let ast = self.check_error_ptr(
            unsafe {
                Z3_mk_numeral(*ctx, bv_cstring.as_ptr(), *sort)
            }
        )?;
        Ok(unsafe { Self::wrap_no_error_check(ctx, ast) })
    }

    pub fn new_const<S: Into<Symbol>>(ctx: &'ctx Context, name: S, sz: u32) -> BV<'ctx> {
        let sort = Sort::bitvector(ctx, sz);
        let name_sym = name.into().as_z3_symbol(ctx);
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_const(*ctx, name_sym, *sort)
            })
        }
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str, sz: u32) -> BV<'ctx> {
        let sort = Sort::bitvector(ctx, sz);
        let pp = CString::new(prefix).unwrap();
        let p = pp.as_ptr();
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_fresh_const(*ctx, p, *sort)
            })
        }
    }

    pub fn from_i64(ctx: &'ctx Context, i: i64, sz: u32) -> BV<'ctx> {
        let sort = Sort::bitvector(ctx, sz);
        unsafe { Self::wrap_check_error(ctx, Z3_mk_int64(*ctx, i, *sort)) }
    }

    pub fn from_u64(ctx: &'ctx Context, u: u64, sz: u32) -> BV<'ctx> {
        let sort = Sort::bitvector(ctx, sz);
        unsafe { Self::wrap_check_error(ctx, Z3_mk_unsigned_int64(*ctx, u, *sort)) }
    }

    pub fn as_i64(&self) -> Option<i64> {
        let mut out:i64 = 0;
        if self.check_error_pass(unsafe{Z3_get_numeral_int64(**self.ctx(), **self, &mut out)}) {
            Some(out)
        } else { None }
    }

    pub fn as_u64(&self) -> Option<u64> {
        let mut out:u64 = 0;
        if self.check_error_pass(unsafe{Z3_get_numeral_uint64(**self.ctx(), **self, &mut out)}) {
            Some(out)
        } else { None }
    }

    /// Create a bit vector from an integer.
    ///
    /// The bit vector will have width `sz`.
    ///
    /// # Examples
    /// ```
    /// # use z3::{ast, Config, Context, SatResult, Solver};
    /// # use z3::ast::Ast;
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// # let solver = Solver::new(&ctx);
    /// let i = ast::Int::new_const(&ctx, "x");
    /// solver.assert(&i._eq(&ast::Int::from_i64(&ctx, -3)));
    ///
    /// let x = ast::BV::from_int(&i, 64);
    /// assert_eq!(64, x.get_size());
    ///
    /// assert_eq!(solver.check(), SatResult::Sat);
    /// let model = solver.get_model().unwrap();;
    ///
    /// assert_eq!(-3, model.eval(&x.to_int(true), true).unwrap().as_i64().expect("as_i64() shouldn't fail"));
    /// ```
    pub fn from_int(ast: &Int<'ctx>, sz: u32) -> BV<'ctx> {
        unsafe { Self::wrap_check_error(ast.ctx, Z3_mk_int2bv(*ast.ctx(), sz, *ast)) }
    }

    /// Create an integer from a bitvector.
    /// This is just a convenience wrapper around
    /// [`Int::from_bv()`]; see notes there.
    pub fn to_int(&self, signed: bool) -> Int<'ctx> {
        Int::from_bv(self, signed)
    }

    /// Get the size of the bitvector (in bits)
    pub fn get_size(&self) -> u32 {
        let sort = self.get_sort();
        self.check_error_pass(unsafe { Z3_get_bv_sort_size(**self.ctx(), *sort) }).unwrap()
    }

    // Bitwise ops
    unop! {
        /// Bitwise negation
        pub fn bvnot(Z3_mk_bvnot) -> Self;
        /// Two's complement negation
        pub fn bvneg(Z3_mk_bvneg) -> Self;
        /// Conjunction of all the bits in the vector. Returns a BV with size (bitwidth) 1.
        pub fn bvredand(Z3_mk_bvredand) -> Self;
        /// Disjunction of all the bits in the vector. Returns a BV with size (bitwidth) 1.
        pub fn bvredor(Z3_mk_bvredor) -> Self;
    }
    binop! {
        /// Bitwise and
        pub fn bvand(Z3_mk_bvand, a) -> Self;
        /// Bitwise or
        pub fn bvor(Z3_mk_bvor, a) -> Self;
        /// Bitwise exclusive-or
        pub fn bvxor(Z3_mk_bvxor, a) -> Self;
        /// Bitwise nand
        pub fn bvnand(Z3_mk_bvnand, a) -> Self;
        /// Bitwise nor
        pub fn bvnor(Z3_mk_bvnor, a) -> Self;
        /// Bitwise xnor
        pub fn bvxnor(Z3_mk_bvxnor, a) -> Self;
    }

    // Arithmetic ops
    binop! {
        /// Addition
        pub fn bvadd(Z3_mk_bvadd, a) -> Self;
        /// Subtraction
        pub fn bvsub(Z3_mk_bvsub, a) -> Self;
        /// Multiplication
        pub fn bvmul(Z3_mk_bvmul, a) -> Self;
        /// Unsigned division
        pub fn bvudiv(Z3_mk_bvudiv, a) -> Self;
        /// Signed division
        pub fn bvsdiv(Z3_mk_bvsdiv, a) -> Self;
        /// Unsigned remainder
        pub fn bvurem(Z3_mk_bvurem, a) -> Self;
        /// Signed remainder (sign follows dividend)
        pub fn bvsrem(Z3_mk_bvsrem, a) -> Self;
        /// Signed remainder (sign follows divisor)
        pub fn bvsmod(Z3_mk_bvsmod, a) -> Self;
    }

    // Comparison ops
    binop! {
        /// Unsigned less than
        pub fn bvult(Z3_mk_bvult, a) -> Bool<'ctx>;
        /// Signed less than
        pub fn bvslt(Z3_mk_bvslt, a) -> Bool<'ctx>;
        /// Unsigned less than or equal
        pub fn bvule(Z3_mk_bvule, a) -> Bool<'ctx>;
        /// Signed less than or equal
        pub fn bvsle(Z3_mk_bvsle, a) -> Bool<'ctx>;
        /// Unsigned greater or equal
        pub fn bvuge(Z3_mk_bvuge, a) -> Bool<'ctx>;
        /// Signed greater or equal
        pub fn bvsge(Z3_mk_bvsge, a) -> Bool<'ctx>;
        /// Unsigned greater than
        pub fn bvugt(Z3_mk_bvugt, a) -> Bool<'ctx>;
        /// Signed greater than
        pub fn bvsgt(Z3_mk_bvsgt, a) -> Bool<'ctx>;
    }

    // Shift ops
    binop! {
        /// Shift left
        pub fn bvshl(Z3_mk_bvshl, a) -> Self;
        /// Logical shift right (add zeroes in the high bits)
        pub fn bvlshr(Z3_mk_bvlshr, a) -> Self;
        /// Arithmetic shift right (sign-extend in the high bits)
        pub fn bvashr(Z3_mk_bvashr, a) -> Self;
        /// Rotate left
        pub fn bvrotl(Z3_mk_ext_rotate_left, a) -> Self;
        /// Rotate right
        pub fn bvrotr(Z3_mk_ext_rotate_right, a) -> Self;
    }

    binop! {
        /// Concatenate two bitvectors
        pub fn concat(Z3_mk_concat, a) -> Self;
    }

    // overflow checks
    unop! {
        /// Check if negation overflows
        pub fn bvneg_no_overflow(Z3_mk_bvneg_no_overflow) -> Bool<'ctx>;
    }
    bv_overflow_check_signed! {
        /// Check if addition overflows
        pub fn bvadd_no_overflow(Z3_mk_bvadd_no_overflow);
        /// Check if subtraction underflows
        pub fn bvsub_no_underflow(Z3_mk_bvsub_no_underflow);
        /// Check if multiplication overflows
        pub fn bvmul_no_overflow(Z3_mk_bvmul_no_overflow);
    }
    binop! {
        /// Check if addition underflows
        pub fn bvadd_no_underflow(Z3_mk_bvadd_no_underflow, a) -> Bool<'ctx>;
        /// Check if subtraction overflows
        pub fn bvsub_no_overflow(Z3_mk_bvsub_no_overflow, a) -> Bool<'ctx>;
        /// Check if signed division overflows
        pub fn bvsdiv_no_overflow(Z3_mk_bvsdiv_no_overflow, a) -> Bool<'ctx>;
        /// Check if multiplication underflows
        pub fn bvmul_no_underflow(Z3_mk_bvmul_no_underflow, a) -> Bool<'ctx>;
    }

    /// Extract the bits `high` down to `low` from the bitvector.
    /// Returns a bitvector of size `n`, where `n = high - low + 1`.
    pub fn extract(&self, high: u32, low: u32) -> Self {
        unsafe {
            Self::wrap_check_error(self.ctx, {
                Z3_mk_extract(**self.ctx(), high, low, **self)
            })
        }
    }

    /// Sign-extend the bitvector to size `m+i`, where `m` is the original size of the bitvector.
    /// That is, `i` bits will be added.
    pub fn sign_ext(&self, i: u32) -> Self {
        unsafe {
            Self::wrap_check_error(self.ctx, {
                Z3_mk_sign_ext(**self.ctx(), i, **self)
            })
        }
    }

    /// Zero-extend the bitvector to size `m+i`, where `m` is the original size of the bitvector.
    /// That is, `i` bits will be added.
    pub fn zero_ext(&self, i: u32) -> Self {
        unsafe {
            Self::wrap_check_error(self.ctx, {
                Z3_mk_zero_ext(**self.ctx(), i, **self)
            })
        }
    }
}

impl<'ctx> Array<'ctx> {
    /// Create an `Array` which maps from indices of the `domain` `Sort` to
    /// values of the `range` `Sort`.
    ///
    /// All values in the `Array` will be unconstrained.
    pub fn new_const<S: Into<Symbol>>(
        ctx: &'ctx Context,
        name: S,
        domain: &Sort<'ctx>,
        range: &Sort<'ctx>,
    ) -> Array<'ctx> {
        let sort = Sort::array(ctx, domain, range);
        let sym = name.into().as_z3_symbol(ctx);
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_const(*ctx, sym, *sort)
            })
        }
    }

    pub fn fresh_const(
        ctx: &'ctx Context,
        prefix: &str,
        domain: &Sort<'ctx>,
        range: &Sort<'ctx>,
    ) -> Array<'ctx> {
        let sort = Sort::array(ctx, domain, range);
        let pp = CString::new(prefix).unwrap();
        let p = pp.as_ptr();
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_fresh_const(*ctx, p, *sort)
            })
        }
    }

    /// Create a "constant array", that is, an `Array` initialized so that all of the
    /// indices in the `domain` map to the given value `val`
    pub fn const_array<A>(ctx: &'ctx Context, domain: &Sort<'ctx>, val: &A) -> Array<'ctx>
    where
        A: Ast<'ctx>,
    {
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_const_array(*ctx, *domain, *val)
            })
        }
    }

    /// Get the value at a given index in the array.
    ///
    /// Note that the `index` _must be_ of the array's `domain` sort.
    /// The return type will be of the array's `range` sort.
    //
    // We avoid the binop! macro because the argument has a non-Self type
    pub fn select<A>(&self, index: &A) -> Dynamic<'ctx>
    where
        A: Ast<'ctx>,
    {
        // TODO: We could validate here that the index is of the correct type.
        // This would require us either to keep around the original `domain` argument
        // from when the Array was constructed, or to do an additional Z3 query
        // to find the domain sort first.
        // But if we did this check ourselves, we'd just panic, so it doesn't seem
        // like a huge advantage over just letting Z3 panic itself when it discovers the
        // problem.
        // This way we also avoid the redundant check every time this method is called.
        unsafe {
            Dynamic::wrap_check_error(self.ctx, {
                Z3_mk_select(**self.ctx(), **self, *index)
            })
        }
    }

    /// n-ary Array read. `idxs` are the indices of the array that gets read.
    /// This is useful for applying lambdas.
    pub fn select_n(&self, idxs: &[&dyn Ast]) -> Dynamic<'ctx> {
        let idxs: Vec<NonNull<Z3_ast>> = idxs.iter().map(|idx| *idx).collect();

        unsafe {
            Dynamic::wrap_check_error(self.ctx, {
                Z3_mk_select_n(
                    **self.ctx(),
                    **self,
                    idxs.len().try_into().unwrap(),
                    idxs.as_ptr() as *const Z3_ast,
                )
            })
        }
    }

    /// Update the value at a given index in the array.
    ///
    /// Note that the `index` _must be_ of the array's `domain` sort,
    /// and the `value` _must be_ of the array's `range` sort.
    //
    // We avoid the trinop! macro because the arguments have non-Self types
    pub fn store<A1, A2>(&self, index: &A1, value: &A2) -> Self
    where
        A1: Ast<'ctx>,
        A2: Ast<'ctx>,
    {
        unsafe {
            Self::wrap_check_error(self.ctx, {
                Z3_mk_store(
                    **self.ctx(),
                    **self,
                    *index,
                    *value,
                )
            })
        }
    }

    /// Returns true if the array is a const array (i.e. `a.is_const_array() => exists v, forall i. select(a, i) == v`)
    ///
    /// # Examples
    /// ```
    /// # use z3::{ast, Config, Context, ast::{Array, Int}, Sort};
    /// # use z3::ast::Ast;
    /// # use std::convert::TryInto;
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// let arr = Array::const_array(&ctx, &Sort::int(&ctx), &Int::from_u64(&ctx, 9));
    /// assert!(arr.is_const_array());
    /// let arr2 = Array::fresh_const(&ctx, "a", &Sort::int(&ctx), &Sort::int(&ctx));
    /// assert!(!arr2.is_const_array());
    /// ```
    pub fn is_const_array(&self) -> bool {
        // python:
        // is_app_of(a, Z3_OP_CONST_ARRAY)
        // >> is_app(a) and a.decl().kind() == Z3_OP_CONST_ARRAY
        self.is_app() && matches!(self.decl().kind(), DeclKind::CONST_ARRAY)
    }
}

impl<'ctx> Set<'ctx> {
    pub fn new_const<S: Into<Symbol>>(
        ctx: &'ctx Context,
        name: S,
        eltype: &Sort<'ctx>,
    ) -> Set<'ctx> {
        let sort = Sort::set(ctx, eltype);
        let sym = name.into().as_z3_symbol(ctx);
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_const(*ctx, sym, *sort)
            })
        }
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str, eltype: &Sort<'ctx>) -> Set<'ctx> {
        let sort = Sort::set(ctx, eltype);
        let pp = CString::new(prefix).unwrap();
        let p = pp.as_ptr();
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_fresh_const(*ctx, p, *sort)
            })
        }
    }

    /// Creates a set that maps the domain to false by default
    pub fn empty(ctx: &'ctx Context, domain: &Sort<'ctx>) -> Set<'ctx> {
        unsafe { Self::wrap_check_error(ctx, Z3_mk_empty_set(*ctx, *domain)) }
    }

    /// Add an element to the set.
    ///
    /// Note that the `element` _must be_ of the `Set`'s `eltype` sort.
    //
    // We avoid the binop! macro because the argument has a non-Self type
    pub fn add<A>(&self, element: &A) -> Set<'ctx>
    where
        A: Ast<'ctx>,
    {
        unsafe {
            Self::wrap_check_error(self.ctx, {
                Z3_mk_set_add(**self.ctx(), **self, *element)
            })
        }
    }

    /// Remove an element from the set.
    ///
    /// Note that the `element` _must be_ of the `Set`'s `eltype` sort.
    //
    // We avoid the binop! macro because the argument has a non-Self type
    pub fn del<A>(&self, element: &A) -> Set<'ctx>
    where
        A: Ast<'ctx>,
    {
        unsafe {
            Self::wrap_check_error(self.ctx, {
                Z3_mk_set_del(**self.ctx(), **self, *element)
            })
        }
    }

    /// Check if an item is a member of the set.
    ///
    /// Note that the `element` _must be_ of the `Set`'s `eltype` sort.
    //
    // We avoid the binop! macro because the argument has a non-Self type
    pub fn member<A>(&self, element: &A) -> Bool<'ctx>
    where
        A: Ast<'ctx>,
    {
        unsafe {
            Bool::wrap_check_error(self.ctx, {
                Z3_mk_set_member(**self.ctx(), *element, **self)
            })
        }
    }

    varop! {
        /// Take the intersection of a list of sets.
        pub fn intersect(Z3_mk_set_intersect, ...) -> Self;
        /// Take the union of a list of sets.
        pub fn set_union(Z3_mk_set_union, ...) -> Self;
    }
    unop! {
        /// Take the complement of the set.
        pub fn complement(Z3_mk_set_complement) -> Self;
    }
    binop! {
        /// Check if the set is a subset of another set.
        pub fn set_subset(Z3_mk_set_subset, a) -> Bool<'ctx>;
        /// Take the set difference between two sets.
        pub fn difference(Z3_mk_set_difference, a) -> Self;
    }
}

impl<'ctx> Dynamic<'ctx> {
    pub fn from_ast(ast: impl Ast<'ctx>) -> Self {
        unsafe { Self::wrap_check_error(ast.ctx(), *ast) }
    }

    pub fn new_const<S: Into<Symbol>>(ctx: &'ctx Context, name: S, sort: &Sort<'ctx>) -> Self {
        let sym = name.into().as_z3_symbol(ctx);
        unsafe {
            Self::wrap_check_error(
                ctx,
                Z3_mk_const(*ctx, sym, *sort),
            )
        }
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str, sort: &Sort<'ctx>) -> Self {
        let pp = CString::new(prefix).unwrap();
        let p = pp.as_ptr();
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_fresh_const(*ctx, p, *sort)
            })
        }
    }

    pub fn sort_kind(&self) -> SortKind {
        self.check_error_pass(unsafe { Z3_get_sort_kind(**self.ctx(), Z3_get_sort(**self.ctx(), **self)) }).unwrap()
    }

    /// Returns `None` if the `Dynamic` is not actually a `Bool`
    pub fn as_bool(&self) -> Option<Bool<'ctx>> {
        match self.sort_kind() {
            SortKind::Bool => Some(unsafe { Bool::wrap(self.ctx, **self) }),
            _ => None,
        }
    }

    /// Returns `None` if the `Dynamic` is not actually an `Int`
    pub fn as_int(&self) -> Option<Int<'ctx>> {
        match self.sort_kind() {
            SortKind::Int => Some(unsafe { Int::wrap(self.ctx, **self) }),
            _ => None,
        }
    }

    /// Returns `None` if the `Dynamic` is not actually a `Real`
    pub fn as_real(&self) -> Option<Real<'ctx>> {
        match self.sort_kind() {
            SortKind::Real => Some(unsafe { Real::wrap(self.ctx, **self) }),
            _ => None,
        }
    }

    /// Returns `None` if the `Dynamic` is not actually a `Float`
    pub fn as_float(&self) -> Option<Float<'ctx>> {
        match self.sort_kind() {
            SortKind::FloatingPoint => Some(unsafe { Float::wrap(self.ctx, **self) }),
            _ => None,
        }
    }

    /// Returns `None` if this is not actually a `FuncDecl`
    pub fn as_func_decl(&self) -> Option<FuncDecl<'ctx>> {
        if self.kind() != AstKind::FuncDecl { return None; }
        Some(unsafe { FuncDecl::wrap(self.ctx(), **self) })
    }

    fn sort_ptr(&self) -> NonNull<Z3_sort> {
        self.check_error_ptr(unsafe { Z3_get_sort(**self.ctx(), **self) }).unwrap()
    }

    /// Returns `None` if the `Dynamic` is not actually a `String`
    pub fn as_string(&self) -> Option<String<'ctx>> {
        let sort = self.sort_ptr();
        let is_string_sort = self.check_error_pass(unsafe { Z3_is_string_sort(**self.ctx(), sort) }).unwrap();
        if is_string_sort {
            Some(unsafe { String::wrap(self.ctx, **self) })
        } else {
            None
        }
    }

    /// Returns `None` if the `Dynamic` is not actually a `BV`
    pub fn as_bv(&self) -> Option<BV<'ctx>> {
        match self.sort_kind() {
            SortKind::BV => Some(unsafe { BV::wrap(self.ctx, **self) }),
            _ => None,
        }
    }

    /// Returns `None` if the `Dynamic` is not actually an `Array`
    pub fn as_array(&self) -> Option<Array<'ctx>> {
        match self.sort_kind() {
            SortKind::Array => Some(unsafe { Array::wrap(self.ctx, **self) }),
            _ => None,
        }
    }

    /// Returns `None` if the `Dynamic` is not actually a `Set`
    pub fn as_set(&self) -> Option<Set<'ctx>> {
        if self.sort_kind() != SortKind::Array { return None; }
        let sort = self.sort_ptr();
        let sort_range = self.check_error_ptr(unsafe { Z3_get_array_sort_range(**self.ctx(), sort) }).unwrap();
        let sort_kind = self.check_error_pass(unsafe { Z3_get_sort_kind(**self.ctx(), sort_range) }).unwrap();
        if sort_kind != SortKind::Bool { return None; }
        Some(unsafe { Set::wrap(self.ctx, **self) })
    }

    /// Returns `None` if the `Dynamic` is not actually a `Datatype`
    pub fn as_datatype(&self) -> Option<Datatype<'ctx>> {
        if self.sort_kind() != SortKind::Datatype { return None; }
        Some(unsafe { Datatype::wrap(self.ctx, **self) })
    }

    pub fn is_as_array(&self) -> bool {
        self.check_error_wrap(unsafe { Z3_is_as_array(self.ctx, **self) }).unwrap()
    }
}

impl<'ctx> Datatype<'ctx> {
    pub fn new_const<S: Into<Symbol>>(ctx: &'ctx Context, name: S, sort: &Sort<'ctx>) -> Self {
        assert_eq!(ctx, sort.ctx);
        assert_eq!(sort.kind(), SortKind::Datatype);

        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(*ctx, name.into().as_z3_symbol(ctx), *sort)
            })
        }
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str, sort: &Sort<'ctx>) -> Self {
        assert_eq!(ctx, sort.ctx);
        assert_eq!(sort.kind(), SortKind::Datatype);
        let pp = CString::new(prefix).unwrap();
        let p = pp.as_ptr();
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_fresh_const(*ctx, p, *sort)
            })
        }
    }
}

impl<'ctx> Regexp<'ctx> {
    /// Creates a regular expression that recognizes the string given as parameter
    pub fn literal(ctx: &'ctx Context, s: &str) -> Self {
        let c_str = CString::new(s).unwrap();
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_seq_to_re(*ctx, Z3_mk_string(*ctx, c_str.as_ptr()))
            })
        }
    }

    /// Creates a regular expression that recognizes a character in the specified range (e.g.
    /// `[a-z]`)
    pub fn range(ctx: &'ctx Context, lo: &char, hi: &char) -> Self {
        let lo_ast = StringAst::from_const(lo);
        let hi_ast = StringAst::from_const(hi);
        unsafe {
            Self::wrap_check_error(ctx, Z3_mk_re_range(*ctx, *lo_ast, *hi_ast))
        }
    }

    /// Creates a regular expression that recognizes this regular expression `lo` to `hi` times (e.g. `a{2,3}`)
    ///
    /// Renamed from "loop" as that is a reserved keyword in rust.
    pub fn times(&self, lo: u32, hi: u32) -> Self {
        unsafe {
            Self::wrap_check_error(self.ctx, {
                Z3_mk_re_loop(**self.ctx(), **self, lo, hi)
            })
        }
    }

    /// Creates a regular expression that recognizes this regular expression
    /// n number of times
    /// Requires Z3 4.8.15 or later.
    pub fn power(&self, n: u32) -> Self {
        unsafe {
            Self::wrap_check_error(self.ctx, {
                Z3_mk_re_power(**self.ctx(), **self, n)
            })
        }
    }

    /// The regex sort
    ///
    /// Equivalent to `Z3_mk_re_sort(Z3_mk_string_sort())`
    pub fn sort(ctx: &'ctx Context) -> Sort<'ctx> {
        let string_sort = self.check_error_ptr(unsafe { Z3_mk_string_sort(*ctx) }).unwrap();
        unsafe { Sort::wrap_check_error(ctx, Z3_mk_re_sort(*ctx, string_sort)) }
    }

    /// Creates a regular expression that recognizes all sequences
    pub fn full(ctx: &'ctx Context) -> Self {
        unsafe {
            Self::wrap_check_error(ctx, Z3_mk_re_full(
                    *ctx,
                    *Self::sort(ctx),
                )
            )
        }
    }

    /// Creates a regular expression that accepts all singleton sequences of the characters
    ///
    /// Requires Z3 4.8.13 or later.
    pub fn allchar(ctx: &'ctx Context) -> Self {
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_re_allchar(
                    *ctx,
                    *Self::sort(ctx),
                )
            })
        }
    }

    /// Creates a regular expression that doesn't recognize any sequences
    pub fn empty(ctx: &'ctx Context) -> Self {
        unsafe {
            Self::wrap_check_error(ctx, {
                Z3_mk_re_empty(
                    *ctx,
                    *Self::sort(ctx),
                )
            })
        }
    }

    unop! {
       /// Creates a regular expression that recognizes this regular expression one or more times (e.g. `a+`)
       pub fn plus(Z3_mk_re_plus) -> Self;
       /// Creates a regular expression that recognizes this regular expression any number of times
       /// (Kleene star, e.g. `a*`)
       pub fn star(Z3_mk_re_star) -> Self;
       /// Creates a regular expression that recognizes any sequence that this regular expression
       /// doesn't
       pub fn complement(Z3_mk_re_complement) -> Self;
       /// Creates a regular expression that optionally accepts this regular expression (e.g. `a?`)
       pub fn option(Z3_mk_re_option) -> Self;
    }
    binop! {
        /// Creates a difference regular expression
        /// Requires Z3 4.8.14 or later.
        pub fn diff(Z3_mk_re_diff, a) -> Self;
    }
    varop! {
        /// Concatenates regular expressions
        pub fn concat(Z3_mk_re_concat, ...) -> Self;
        /// Creates a regular expression that recognizes sequences that any of the regular
        /// expressions given as parameters recognize
        pub fn union(Z3_mk_re_union, ...) -> Self;
        /// Creates a regular expression that only recognizes sequences that all of the parameters
        /// recognize
        pub fn intersect(Z3_mk_re_intersect, ...) -> Self;
    }
}

/// Create a universal quantifier.
///
/// # Examples
/// ```
/// # use z3::{ast, Config, Context, FuncDecl, Pattern, SatResult, Solver, Sort, Symbol};
/// # use z3::ast::Ast;
/// # use std::convert::TryInto;
/// # let cfg = Config::new();
/// # let ctx = Context::new(&cfg);
/// # let solver = Solver::new(&ctx);
/// let f = FuncDecl::new(&ctx, "f", &[&Sort::int(&ctx)], &Sort::int(&ctx));
///
/// let x = ast::Int::new_const(&ctx, "x");
/// let f_x: ast::Int = f.apply(&[&x]).try_into().unwrap();
/// let f_x_pattern: Pattern = Pattern::new(&ctx, &[ &f_x ]);
/// let forall: ast::Bool = ast::forall_const(
///     &ctx,
///     &[&x],
///     &[&f_x_pattern],
///     &x._eq(&f_x)
/// ).try_into().unwrap();
/// solver.assert(&forall);
///
/// assert_eq!(solver.check(), SatResult::Sat);
/// let model = solver.get_model().unwrap();;
///
/// let f_f_3: ast::Int = f.apply(&[&f.apply(&[&ast::Int::from_u64(&ctx, 3)])]).try_into().unwrap();
/// assert_eq!(3, model.eval(&f_f_3, true).unwrap().as_u64().unwrap());
/// ```
pub fn forall_const<'ctx>(
    ctx: &'ctx Context,
    bounds: &[&dyn Ast<'ctx>],
    patterns: &[&Pattern<'ctx>],
    body: &Bool<'ctx>,
) -> Bool<'ctx> {
    assert!(bounds.iter().all(|a| a.ctx() == ctx));
    assert!(patterns.iter().all(|p| p.ctx == ctx));
    assert_eq!(ctx, body.ctx());

    if bounds.is_empty() {
        return body.clone();
    }

    let bounds: Vec<_> = bounds.iter().map(|a| *a).collect();
    let patterns: Vec<_> = patterns.iter().map(|p| *p).collect();

    unsafe {
        Bool::wrap_check_error(ctx, {
            Z3_mk_forall_const(
                *ctx,
                0,
                bounds.len().try_into().unwrap(),
                bounds.as_ptr(),
                patterns.len().try_into().unwrap(),
                patterns.as_ptr(),
                *body,
            )
        })
    }
}

/// Create an existential quantifier.
///
/// # Examples
/// ```
/// # use z3::{ast, Config, Context, FuncDecl, SatResult, Solver, Sort, Symbol, Pattern};
/// # use z3::ast::Ast;
/// # use std::convert::TryInto;
/// # let cfg = Config::new();
/// # let ctx = Context::new(&cfg);
/// # let solver = Solver::new(&ctx);
/// let f = FuncDecl::new(&ctx, "f", &[&Sort::int(&ctx)], &Sort::int(&ctx));
///
/// let x = ast::Int::new_const(&ctx, "x");
/// let f_x: ast::Int = f.apply(&[&x]).try_into().unwrap();
/// let f_x_pattern: Pattern = Pattern::new(&ctx, &[ &f_x ]);
/// let exists: ast::Bool = ast::exists_const(
///     &ctx,
///     &[&x],
///     &[&f_x_pattern],
///     &x._eq(&f_x).not()
/// ).try_into().unwrap();
/// solver.assert(&exists.not());
///
/// assert_eq!(solver.check(), SatResult::Sat);
/// let model = solver.get_model().unwrap();;
///
/// let f_f_3: ast::Int = f.apply(&[&f.apply(&[&ast::Int::from_u64(&ctx, 3)])]).try_into().unwrap();
/// assert_eq!(3, model.eval(&f_f_3, true).unwrap().as_u64().unwrap());
/// ```
pub fn exists_const<'ctx>(
    ctx: &'ctx Context,
    bounds: &[&dyn Ast<'ctx>],
    patterns: &[&Pattern<'ctx>],
    body: &Bool<'ctx>,
) -> Bool<'ctx> {
    assert!(bounds.iter().all(|a| a.ctx() == ctx));
    assert!(patterns.iter().all(|p| p.ctx == ctx));
    assert_eq!(ctx, body.ctx());

    if bounds.is_empty() {
        return body.clone();
    }

    let bounds: Vec<_> = bounds.iter().map(|a| *a).collect();
    let patterns: Vec<_> = patterns.iter().map(|p| p.z3_pattern).collect();

    unsafe {
        Bool::wrap_check_error(ctx, {
            Z3_mk_exists_const(
                *ctx,
                0,
                bounds.len().try_into().unwrap(),
                bounds.as_ptr() as *const Z3_app,
                patterns.len().try_into().unwrap(),
                patterns.as_ptr() as *const Z3_pattern,
                *body,
            )
        })
    }
}

/// Create a lambda expression.
///
/// - `num_decls`: Number of variables to be bound.
/// - `sorts`: Bound variable sorts.
/// - `decl_names`: Contains the names that the quantified formula uses for the bound variables.
/// - `body`: Expression body that contains bound variables of the same sorts as the sorts listed in the array sorts.
///
/// # Examples
/// ```
/// # use z3::{
/// #     ast::{lambda_const, Ast as _, Int, Dynamic},
/// #     Config, Context, Solver, SatResult,
/// # };
/// #
/// # let cfg = Config::new();
/// # let ctx = Context::new(&cfg);
/// # let solver = Solver::new(&ctx);
/// #
/// let input = Int::fresh_const(&ctx, "");
/// let lambda = lambda_const(
///     &ctx,
///     &[&input],
///     &Dynamic::from_ast(&Int::add(&ctx, &[&input, &Int::from_i64(&ctx, 2)])),
/// );
///
/// solver.assert(
///     &lambda.select_n(&[&Int::from_i64(&ctx, 1)]).as_int().unwrap()
///         ._eq(&Int::from_i64(&ctx, 3))
/// );
///
/// assert_eq!(solver.check(), SatResult::Sat);
///
/// solver.assert(
///     &lambda.select_n(&[&Int::from_i64(&ctx, 1)]).as_int().unwrap()
///         ._eq(&Int::from_i64(&ctx, 2))
/// );
///
/// assert_eq!(solver.check(), SatResult::Unsat);
/// ```
pub fn lambda_const<'ctx>(
    ctx: &'ctx Context,
    bounds: &[&dyn Ast<'ctx>],
    body: &Dynamic<'ctx>,
) -> Array<'ctx> {
    let bounds: Vec<_> = bounds.iter().map(|a| *a).collect();

    unsafe {
        Array::wrap_check_error(
            ctx,
            Z3_mk_lambda_const(
                *ctx,
                bounds.len().try_into().unwrap(),
                bounds.as_ptr(),
                *body,
            ),
        )
    }
}

impl IsNotApp {
    pub fn new(kind: AstKind) -> Self {
        Self { kind }
    }

    pub fn kind(&self) -> AstKind {
        self.kind
    }
}

impl fmt::Display for IsNotApp {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "ast node is not a function application, has kind {:?}",
            self.kind()
        )
    }
}
