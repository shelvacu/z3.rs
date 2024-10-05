use std::ops::Index;

use z3_sys::*;

use crate::{Context, make_z3_object};

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
    pub fn new(&'ctx Context) -> Self {
        let p = unsafe ( Z3_mk_ast_vector
