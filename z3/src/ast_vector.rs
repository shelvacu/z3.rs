use std::ops::Index;
use std::iter::Iterator;
use std::convert::TryInto;

use z3_sys::*;

use crate::{Context, WrappedZ3, HasContext, ast::Dynamic, ast::Bool, make_z3_object};

make_z3_object! {
    pub struct AstVector<'ctx>
    where
        sys_ty: Z3_ast_vector,
        inc_ref: Z3_ast_vector_inc_ref,
        dec_ref: Z3_ast_vector_dec_ref,
        to_str: Z3_ast_vector_to_string,
    ;
}

impl<'ctx> AstVector<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        unsafe { Self::wrap_check_error(ctx, Z3_mk_ast_vector(**ctx)) }
    }

    pub fn len(&self) -> u32 {
        self.check_error_pass(unsafe{Z3_ast_vector_size(**self.ctx(), **self)}).unwrap()
    }

    pub fn get(&self, i: u32) -> Option<Dynamic<'ctx>> {
        if i >= self.len() { return None }
        Some(unsafe { self.get_unchecked(i) })
    }
    
    pub fn push(&self, item: &Dynamic<'ctx>) {
        unsafe { Z3_ast_vector_push(**self.ctx(), **self, **item) };
        self.check_error().unwrap();
    }

    pub unsafe fn get_unchecked(&self, i: u32) -> Dynamic<'ctx> {
        let p = unsafe { Z3_ast_vector_get(**self.ctx(), **self, i) };
        let p = self.check_error_ptr(p).unwrap();
        unsafe { Dynamic::wrap(self.ctx(), p) }
    }

    pub fn iter(&self) -> impl Iterator<Item = Dynamic<'ctx>> {
        AstIter {
            vec: self.clone(),
            idx: 0,
        }
    }
}

struct AstIter<'ctx> {
    vec: AstVector<'ctx>,
    idx: u32,
}

impl<'ctx> Iterator for AstIter<'ctx> {
    type Item = Dynamic<'ctx>;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.idx >= self.vec.len() { return None; }
        let res = self.vec.get(self.idx).unwrap();
        self.idx += 1;
        Some(res)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.idx >= self.vec.len() { return (0, Some(0)); }
        let len:usize = (self.vec.len() - self.idx).try_into().unwrap();
        (len, Some(len))
    }
}
