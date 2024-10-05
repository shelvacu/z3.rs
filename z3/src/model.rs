use std::ptr::NonNull;
use std::mem::MaybeUninit;

use z3_sys::*;

use crate::{Context, FuncInterp, Optimize, Solver, make_z3_object};
use crate::ast::{Ast, FuncDecl, Dynamic};

make_z3_object! {
    /// Model for the constraints inserted into the logical context.
    pub struct Model<'ctx> 
    where
        sys_ty: Z3_model,
        inc_ref: Z3_model_inc_ref,
        dec_ref: Z3_model_dec_ref,
        to_str: Z3_model_to_string,
    ;
}

impl<'ctx> Model<'ctx> {
    pub fn of_solver(slv: &Solver<'ctx>) -> Option<Model<'ctx>> {
        let m = unsafe { Z3_solver_get_model(*slv.ctx(), *slv) };
        let m = slv.check_error_ptr(m).ok()?;
        Some(unsafe{Self::wrap(slv.ctx(), m)})
    }

    pub fn of_optimize(opt: &Optimize<'ctx>) -> Option<Model<'ctx>> {
        let m = unsafe { Z3_optimize_get_model(*opt.ctx(), *opt) };
        let m = opt.check_error_ptr(m).ok()?;
        Some(unsafe { Self::wrap(opt.ctx(), m) })
    }

    /// Translate model to context `dest`
    pub fn translate<'dest_ctx>(&self, dest: &'dest_ctx Context) -> Model<'dest_ctx> {
        unsafe {
            Model::wrap_check_error(
                dest,
                Z3_model_translate(**self.ctx(), **self, dest.z3_ctx),
            )
        }
    }

    /// Returns the interpretation of the given `ast` in the `Model`
    /// Returns `None` if there is no interpretation in the `Model`
    pub fn get_const_interp<T: Ast<'ctx>>(&self, ast: &T) -> Option<T> {
        let func = ast.safe_decl().ok()?;
        let ret =
            unsafe { Z3_model_get_const_interp(**self.ctx(), **self, *func) };
        let res = self.check_error_ptr(ret).ok()?;
        Some(unsafe { T::wrap(self.ctx(), ret) })
    }

    /// Returns the interpretation of the given `f` in the `Model`
    /// Returns `None` if there is no interpretation in the `Model`
    pub fn get_func_interp(&self, f: &FuncDecl) -> Option<FuncInterp<'ctx>> {
        if f.arity() == 0 {
            let ret = unsafe {
                Dynamic::wrap(self.ctx(), Z3_model_get_const_interp(**self.ctx(), **self, *f))
            };
            if !ret.is_as_array() { return None; }
            let range = f.range();
            let sort_kind = range.kind();
            if sort_kind != SortKind::Array { return None; }
            let fd = unsafe {
                FuncDecl::wrap_check_error(
                    self.ctx,
                    Z3_get_as_array_func_decl(**self.ctx(), *ret),
                )
            };
            self.get_func_interp(&fd)
        } else {
            let ret =
                unsafe { Z3_model_get_func_interp(**self.ctx(), **self, f.z3_func_decl) };
            let ret = self.check_error_ptr(ret).ok()?;
            Some(unsafe { FuncInterp::wrap(self.ctx, ret) })
        }
    }

    pub fn eval<T>(&self, ast: &T, model_completion: bool) -> Option<T>
    where
        T: Ast<'ctx>,
    {
        let tmp:MaybeUninit<NonNull<Z3_ast>> = MaybeUninit::uninit();
        let res = {
            unsafe {
                Z3_model_eval(
                    **self.ctx(),
                    **self,
                    *ast,
                    model_completion,
                    &mut tmp,
                )
            }
        };
        self.check_error().unwrap();
        if res {
            Some(unsafe { T::wrap(self.ctx(), tmp.assume_init()) })
        } else {
            None
        }
    }

    fn num_consts(&self) -> u32 {
        let num_consts = unsafe { Z3_model_get_num_consts(**self.ctx(), **self) };
        self.check_error().unwrap();
        num_consts
    }

    fn num_funcs(&self) -> u32 {
        let num_funcs = unsafe { Z3_model_get_num_funcs(**self.ctx(), **self) };
        self.check_error().unwrap();
        num_funcs
    }

    fn len(&self) -> u32 {
        self.num_consts() + self.num_funcs()
    }

    pub fn iter(&'ctx self) -> ModelIter<'ctx> {
        self.into_iter()
    }
}

#[derive(Debug)]
/// <https://z3prover.github.io/api/html/classz3py_1_1_model_ref.html#a7890b7c9bc70cf2a26a343c22d2c8367>
pub struct ModelIter<'ctx> {
    model: &'ctx Model<'ctx>,
    idx: u32,
    len: u32,
}

impl<'ctx> IntoIterator for &'ctx Model<'ctx> {
    type Item = FuncDecl<'ctx>;
    type IntoIter = ModelIter<'ctx>;

    fn into_iter(self) -> Self::IntoIter {
        ModelIter {
            model: self,
            idx: 0,
            len: self.len(),
        }
    }
}

impl<'ctx> Iterator for ModelIter<'ctx> {
    type Item = FuncDecl<'ctx>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx >= self.len {
            return None;
        }
        let num_consts = self.model.num_consts();
        let decl = if self.idx < num_consts {
            unsafe {
                Z3_model_get_const_decl(**self.model.ctx(), **self.model, self.idx)
            }
        } else {
            unsafe {
                Z3_model_get_func_decl(
                    **self.model.ctx(),
                    **self.model,
                    self.idx - num_consts,
                )
            }
        };
        self.idx += 1;
        Some(unsafe { FuncDecl::wrap_check_error(**self.model.ctx(), decl) })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = (self.len - self.idx) as usize;
        (len, Some(len))
    }
}

#[test]
fn test_unsat() {
    use crate::{ast, Config, SatResult};
    let cfg = Config::new();
    let ctx = Context::new(cfg);
    let solver = Solver::new(&ctx);
    solver.assert(&ast::Bool::from_bool(&ctx, false));
    assert_eq!(solver.check(), SatResult::Unsat);
    assert!(solver.get_model().is_none());
}
