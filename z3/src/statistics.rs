use std::fmt;

use z3_sys::*;

use crate::{HasContext, make_z3_object};

/// The value for a key in [`Statistics`].
///
/// # See also:
///
/// - [`StatisticsEntry`]
/// - [`Statistics::value`]
#[derive(Clone, Debug)]
pub enum StatisticsValue {
    UInt(u32),
    Double(f64),
}

make_z3_object! {
    /// Statistical data about a solver.
    ///
    /// # See also:
    ///
    /// - [`Optimize::get_statistics()`]
    /// - [`Solver::get_statistics()`]
    pub struct Statistics<'ctx>
    where
        sys_ty: Z3_stats,
        inc_ref: Z3_stats_inc_ref,
        dec_ref: Z3_stats_dec_ref,
    ;
}

impl<'ctx> Statistics<'ctx> {
    /// Get the statistics value at the given index.
    ///
    /// # Safety:
    ///
    /// This assumes that `idx` is a valid index.
    fn value_at_idx(&self, idx: u32) -> StatisticsValue {
        if self.check_error_pass(unsafe { Z3_stats_is_uint(**self.ctx(), **self, idx) }).unwrap() {
            StatisticsValue::UInt(self.check_error_pass(unsafe { Z3_stats_get_uint_value(**self.ctx(), **self, idx) }).unwrap())
        } else {
            StatisticsValue::Double(self.check_error_pass(unsafe { Z3_stats_get_double_value(
                **self.ctx(),
                **self,
                idx,
            )}).unwrap())
        }
    }

    fn key_at_idx(&self, idx: u32) -> String {
        self.check_error_str(unsafe { Z3_stats_get_key(**self.ctx(), **self, idx) })
    }

    pub fn len(&self) -> u32 {
        self.check_error_pass(unsafe { Z3_stats_size(**self.ctx(), **self) }).unwrap()
    }

    /// Get the statistics value for the given `key`.
    pub fn value(&self, key: &str) -> Option<StatisticsValue> {
        self.entries().find_map(move |(k, v)| if k.as_str() == key { Some(v) } else { None })
    }

    /// Iterate over all of the entries in this set of statistics.
    pub fn entries(&self) -> impl Iterator<Item = (String, StatisticsValue)> + '_ {
        (0..self.len()).map(move |n| (self.key_at_idx(n), self.value_at_idx(n)))
    }
}

impl<'ctx> fmt::Display for Statistics<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "<z3.stats>")
    }
}

impl<'ctx> fmt::Debug for Statistics<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let mut s = f.debug_struct("Statistics");
        for (k, v) in self.entries() {
            match v {
                StatisticsValue::UInt(v) => s.field(&k, &v),
                StatisticsValue::Double(v) => s.field(&k, &v),
            };
        }
        s.finish()
    }
}
