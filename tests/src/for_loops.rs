//@ [!lean] skip
//@ [lean] aeneas-args=-lean-for-loops

/// Test for native Lean 4 `for x in xs do` extraction.
/// These tests verify that Rust for-loops over iterators are extracted
/// as native Lean for-loops when the `-lean-for-loops` flag is used.

/// No-op annotation: marks a loop invariant for Aeneas.
/// Aeneas emits this as a `-- loop_invariant: ...` comment in the Lean output.
pub fn loop_invariant<P: Fn() -> bool>(_inv: P) {}

/// Simple for-loop: copy one array into another.
pub fn copy_arrays(src: &[u8; 256], dst: &mut [u8; 256]) {
    for i in 0usize..256 {
        dst[i] = src[i];
    }
}

/// For-loop with a loop-invariant annotation.
pub fn copy_arrays_with_inv(src: &[u8; 256], dst: &mut [u8; 256]) {
    for i in 0usize..256 {
        loop_invariant(|| true);
        dst[i] = src[i];
    }
}

/// For-loop with an invariant referencing the loop counter and a running sum.
/// The invariant is placed inside the loop, so the loop counter `i` is in scope.
pub fn sum_with_inv(arr: &[u8; 256]) -> u32 {
    let mut sum: u32 = 0;
    let mut count: usize = 0;
    for i in 0usize..256 {
        loop_invariant(|| (sum as usize) <= i * 255);
        sum += arr[i] as u32;
        count = i + 1;
    }
    sum
}
