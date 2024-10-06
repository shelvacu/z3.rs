//! Helpers for building custom [datatype sorts](DatatypeSort).

use std::{convert::TryInto, ptr::{null_mut, NonNull}};

use z3_sys::*;

use crate::{
    Context, HasContext, WrappedZ3,
    Symbol,
};
use crate::ast::{FuncDecl, Sort};

/// Build a custom [datatype sort](DatatypeSort).
///
/// Example:
/// ```
/// # use z3::{ast::Int, Config, Context, DatatypeAccessor, DatatypeBuilder, SatResult, Solver, Sort, ast::{Ast, Datatype}};
/// # let cfg = Config::new();
/// # let ctx = Context::new(&cfg);
/// # let solver = Solver::new(&ctx);
/// // Like Rust's Option<int> type
/// let option_int = DatatypeBuilder::new(&ctx, "OptionInt")
/// .variant("None", vec![])
/// .variant(
///     "Some",
///     vec![("value", DatatypeAccessor::Sort(Sort::int(&ctx)))],
/// )
/// .finish();
///
/// // Assert x.is_none()
/// let x = Datatype::new_const(&ctx, "x", &option_int.sort);
/// solver.assert(&option_int.variants[0].tester.apply(&[&x]).as_bool().unwrap());
///
/// // Assert y == Some(3)
/// let y = Datatype::new_const(&ctx, "y", &option_int.sort);
/// let value = option_int.variants[1].constructor.apply(&[&Int::from_i64(&ctx, 3)]);
/// solver.assert(&y._eq(&value.as_datatype().unwrap()));
///
/// assert_eq!(solver.check(), SatResult::Sat);
/// let model = solver.get_model().unwrap();;
///
/// // Get the value out of Some(3)
/// let ast = option_int.variants[1].accessors[0].apply(&[&y]);
/// assert_eq!(3, model.eval(&ast.as_int().unwrap(), true).unwrap().as_i64().unwrap());
/// ```
#[derive(Debug)]
pub struct DatatypeBuilder<'ctx> {
    ctx: &'ctx Context,
    name: Symbol,
    constructors: Vec<(String, Vec<(String, DatatypeAccessor<'ctx>)>)>,
}

impl<'ctx> HasContext<'ctx> for DatatypeBuilder<'ctx> {
    fn ctx(&self) -> &'ctx Context {
        self.ctx
    }
}

/// Wrapper which can point to a sort (by value) or to a custom datatype (by name).
#[derive(Debug)]
pub enum DatatypeAccessor<'ctx> {
    Sort(Sort<'ctx>),
    Datatype(Symbol),
}

/// Inner variant for a custom [datatype sort](DatatypeSort).
#[derive(Debug)]
#[non_exhaustive]
pub struct DatatypeVariant<'ctx> {
    pub constructor: FuncDecl<'ctx>,
    pub tester: FuncDecl<'ctx>,
    pub accessors: Vec<FuncDecl<'ctx>>,
}

impl<'ctx> HasContext<'ctx> for DatatypeVariant<'ctx> {
    fn ctx(&self) -> &'ctx Context {
        self.constructor.ctx()
    }
}

/// A custom datatype sort.
#[derive(Debug)]
#[non_exhaustive]
pub struct DatatypeSort<'ctx> {
    pub sort: Sort<'ctx>,
    pub variants: Vec<DatatypeVariant<'ctx>>,
}

impl<'ctx> HasContext<'ctx> for DatatypeSort<'ctx> {
    fn ctx(&self) -> &'ctx Context {
        self.sort.ctx()
    }
}

impl<'ctx> DatatypeBuilder<'ctx> {
    pub fn new(ctx: &'ctx Context, name: impl Into<Symbol>) -> Self {
        Self {
            ctx,
            name: name.into(),
            constructors: Vec::new(),
        }
    }

    pub fn variant(&mut self, name: &str, fields: Vec<(String, DatatypeAccessor<'ctx>)>) -> &mut Self {
        self.constructors.push((name.to_string(), fields));

        self
    }

    pub fn finish(self) -> DatatypeSort<'ctx> {
        let mut dtypes = create_datatypes(vec![self]);
        dtypes.remove(0)
    }
}

pub fn create_datatypes<'ctx>(
    datatype_builders: Vec<DatatypeBuilder<'ctx>>,
) -> Vec<DatatypeSort<'ctx>> {
    let num = datatype_builders.len();
    assert!(num > 0, "At least one DatatypeBuilder must be specified");

    let ctx: &'ctx Context = datatype_builders[0].ctx;
    let mut names: Vec<NonNull<Z3_symbol>> = Vec::with_capacity(num);

    let mut raw_sorts: Vec<NonNull<Z3_sort>> = Vec::with_capacity(num);
    let mut clists: Vec<NonNull<Z3_constructor_list>> = Vec::with_capacity(num);

    // Collect all the `Z3_constructor`s that we create in here so that we can
    // free them later, once we've created the associated `FuncDecl`s and don't
    // need the raw constructor anymore.
    let mut ctors: Vec<NonNull<Z3_constructor>> = Vec::with_capacity(num * 2);

    for d in datatype_builders.iter() {
        names.push(d.name.as_z3_symbol(ctx));
        let num_cs = d.constructors.len();
        let mut cs: Vec<NonNull<Z3_constructor>> = Vec::with_capacity(num_cs);

        for (cname, fs) in &d.constructors {
            let mut rname: String = "is-".to_string();
            rname.push_str(cname);

            let cname_symbol = Symbol::String(cname.clone()).as_z3_symbol(ctx);
            let rname_symbol = Symbol::String(rname).as_z3_symbol(ctx);

            let num_fs = fs.len();
            let mut field_names: Vec<NonNull<Z3_symbol>> = Vec::with_capacity(num_fs);
            let mut field_sorts: Vec<*mut Z3_sort> = Vec::with_capacity(num_fs);
            let mut sort_refs: Vec<::std::os::raw::c_uint> = Vec::with_capacity(num_fs);

            for (fname, accessor) in fs {
                field_names.push(Symbol::String(fname.clone()).as_z3_symbol(ctx));
                match accessor {
                    DatatypeAccessor::Datatype(dtype_name) => {
                        field_sorts.push(null_mut());

                        let matching_names: Vec<_> = datatype_builders
                            .iter()
                            .enumerate()
                            .filter(|&(_, x)| &x.name == dtype_name)
                            .collect();

                        assert_eq!(
                            1,
                            matching_names.len(),
                            "One and only one occurrence of each datatype is expected."
                        );

                        let (sort_ref, _) = matching_names[0];
                        sort_refs.push(sort_ref as u32);
                    }
                    DatatypeAccessor::Sort(sort) => {
                        field_sorts.push(sort.as_ptr());
                        sort_refs.push(0);
                    }
                }
            }

            let constructor = unsafe {
                Z3_mk_constructor(
                    **ctx,
                    cname_symbol,
                    rname_symbol,
                    num_fs.try_into().unwrap(),
                    field_names.as_ptr(),
                    field_sorts.as_ptr(),
                    sort_refs.as_mut_ptr(),
                )
            };
            cs.push(ctx.check_error_ptr(constructor).unwrap());
        }
        assert!(!cs.is_empty());

        let clist = unsafe {
            Z3_mk_constructor_list(**ctx, num_cs.try_into().unwrap(), cs.as_mut_ptr())
        };
        clists.push(ctx.check_error_ptr(clist).unwrap());
        ctors.extend(cs);
    }

    assert_eq!(num, names.len());
    assert_eq!(num, clists.len());

    unsafe {
        Z3_mk_datatypes(
            **ctx,
            num.try_into().unwrap(),
            names.as_ptr(),
            raw_sorts.as_mut_ptr(),
            clists.as_mut_ptr(),
        );
    }
    ctx.check_error().unwrap();
    unsafe {
        raw_sorts.set_len(num);
    };

    let mut datatype_sorts: Vec<DatatypeSort<'ctx>> = Vec::with_capacity(raw_sorts.len());
    for (z3_sort, datatype_builder) in raw_sorts.into_iter().zip(&datatype_builders) {
        let num_cs = datatype_builder.constructors.len();

        let sort = unsafe { Sort::wrap(ctx, z3_sort) };

        let mut variants: Vec<DatatypeVariant<'ctx>> = Vec::with_capacity(num_cs);

        for (j, (_cname, fs)) in datatype_builder.constructors.iter().enumerate() {
            let num_fs = fs.len();

            let constructor: FuncDecl<'ctx> = unsafe { FuncDecl::wrap_check_error(ctx, Z3_get_datatype_sort_constructor(**ctx, *sort, j.try_into().unwrap())) };

            let tester:FuncDecl<'ctx> = unsafe { FuncDecl::wrap_check_error(ctx, Z3_get_datatype_sort_recognizer(**ctx, *sort, j.try_into().unwrap())) };

            let mut accessors: Vec<FuncDecl<'ctx>> = Vec::new();
            for k in 0..num_fs {
                let accessor_func: *mut Z3_func_decl = unsafe {
                    Z3_get_datatype_sort_constructor_accessor(
                        **ctx,
                        z3_sort,
                        j.try_into().unwrap(),
                        k.try_into().unwrap(),
                    )
                };

                accessors.push(unsafe { FuncDecl::wrap_check_error(ctx, accessor_func) });
            }

            variants.push(DatatypeVariant {
                constructor,
                tester,
                accessors,
            });
        }

        datatype_sorts.push(DatatypeSort { sort, variants });
    }

    for ctor in ctors {
        unsafe {
            Z3_del_constructor(**ctx, ctor);
        }
        ctx.check_error().unwrap();
    }

    for clist in clists {
        unsafe {
            Z3_del_constructor_list(**ctx, clist);
        }
        ctx.check_error().unwrap();
    }

    datatype_sorts
}
