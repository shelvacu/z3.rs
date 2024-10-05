use core::ptr::NonNull;
use std::ffi::CStr;
use std::error::Error as StdError;
use std::fmt;
use crate::Context;
pub use z3_sys::ErrorCode;
use z3_sys::*;

#[derive(Debug, Clone)]
pub struct Error {
    pub code: ErrorCode,
    pub msg: String,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({:?}: {})", self.code, self.msg)
    }
}

impl StdError for Error {}
