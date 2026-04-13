/// No-op annotation recognized by Aeneas when the `-lean-for-loops` flag is used.
///
/// Place this call immediately before a Rust `for` loop to annotate the
/// generated Lean 4 for-loop with a loop invariant comment.
///
/// ```rust
/// let mut sum = 0u32;
/// loop_invariant(|| sum <= u32::MAX);
/// for x in 0..n {
///     sum += x as u32;
/// }
/// ```
///
/// Aeneas will emit:
/// ```lean
/// for x in range do
///   -- loop_invariant: sum ≤ U32.max
///   ...
/// ```
///
/// This function is completely erased at runtime.
#[inline(always)]
pub fn loop_invariant<P: Fn() -> bool>(_inv: P) {}
