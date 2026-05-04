//@ [coq,fstar] skip
//! Regression test: Aeneas used to fail with `Unimplemented` (in
//! `src/interp/InterpJoin.ml`'s `push_abs_for_shared_value`) on functions
//! whose signature contains a shared borrow of a value whose type also
//! contains borrows. The simplest reproducer is a multidimensional borrowed
//! array.

pub fn f(_i: &[&[u8; 10]; 10]) -> usize {
    if false {
        0
    } else {
        0
    }
}

pub fn g(i: &[&u8; 2]) -> u8 {
    *i[0]
}

pub fn h(i: &(&u8, &u8)) -> u8 {
    *i.0 + *i.1
}
