//@ [coq,fstar] skip
//! Regression test for shared borrows of types whose pointee itself
//! contains borrows. The original Aeneas symbolic interpreter rejected
//! such shapes with `Unimplemented` (in `InterpJoin.ml`'s
//! `push_abs_for_shared_value`) and `Found a case of unsupported nested
//! borrows` / `Nested borrows are not supported yet` (in `InterpBorrows.ml`'s
//! `destructure_abs`).

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

pub fn read_inner(i: &[&[u8; 10]; 10]) -> u8 {
    i[0][0]
}

pub fn read_dyn(i: &[&[u8; 10]; 10], a: usize, b: usize) -> u8 {
    i[a][b]
}

pub fn read_first(i: &[&[u8; 10]; 10]) -> u8 {
    *i[0].first().unwrap()
}
