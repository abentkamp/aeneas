//@ [!lean] skip
//@ [lean] aeneas-args=-lean-for-loops

/// Test for native Lean 4 `for x in xs do` extraction.
/// These tests verify that Rust for-loops over iterators are extracted
/// as native Lean for-loops when the `-lean-for-loops` flag is used.

/// Simple for-loop: copy one array into another.
pub fn copy_arrays(src: &[u8; 256], dst: &mut [u8; 256]) {
    for i in 0usize..256 {
        dst[i] = src[i];
    }
}
