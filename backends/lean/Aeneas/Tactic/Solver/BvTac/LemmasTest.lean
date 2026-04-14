import Aeneas.Tactic.Solver.BvTac.BvTac

namespace Aeneas.Std

open Aeneas.Std

-- Test: and_zero via exact BitVec.and_zero (no bv_decide needed)
theorem U8.and_zero_direct (x : U8) : x &&& 0#u8 = 0#u8 := by
  rw [U8.eq_equiv_bv_eq, UScalar.bv_and]; exact BitVec.and_zero

theorem U128.and_zero_direct (x : U128) : x &&& 0#u128 = 0#u128 := by
  rw [U128.eq_equiv_bv_eq, UScalar.bv_and]; exact BitVec.and_zero

-- Test: zero_and via exact BitVec.zero_and
theorem U8.zero_and_direct (x : U8) : 0#u8 &&& x = 0#u8 := by
  rw [U8.eq_equiv_bv_eq, UScalar.bv_and]; exact BitVec.zero_and

theorem U128.zero_and_direct (x : U128) : 0#u128 &&& x = 0#u128 := by
  rw [U128.eq_equiv_bv_eq, UScalar.bv_and]; exact BitVec.zero_and

-- Test: or_zero via exact BitVec.or_zero
theorem U8.or_zero_direct (x : U8) : x ||| 0#u8 = x := by
  rw [U8.eq_equiv_bv_eq, UScalar.bv_or]; exact BitVec.or_zero

theorem U128.or_zero_direct (x : U128) : x ||| 0#u128 = x := by
  rw [U128.eq_equiv_bv_eq, UScalar.bv_or]; exact BitVec.or_zero

-- Test: zero_or via exact BitVec.zero_or
theorem U8.zero_or_direct (x : U8) : 0#u8 ||| x = x := by
  rw [U8.eq_equiv_bv_eq, UScalar.bv_or]; exact BitVec.zero_or

theorem U128.zero_or_direct (x : U128) : 0#u128 ||| x = x := by
  rw [U128.eq_equiv_bv_eq, UScalar.bv_or]; exact BitVec.zero_or

-- Test: xor_eq_zero_iff WITHOUT simp step
theorem U8.xor_eq_zero_no_simp (a b : U8) : a ^^^ b = 0#u8 ↔ a = b := by
  rw [U8.eq_equiv_bv_eq, U8.eq_equiv_bv_eq, UScalar.bv_xor]; exact BitVec.xor_eq_zero_iff

theorem U128.xor_eq_zero_no_simp (a b : U128) : a ^^^ b = 0#u128 ↔ a = b := by
  rw [U128.eq_equiv_bv_eq, U128.eq_equiv_bv_eq, UScalar.bv_xor]; exact BitVec.xor_eq_zero_iff

-- Test: or_eq_zero_iff WITHOUT simp step
theorem U8.or_eq_zero_no_simp (a b : U8) : a ||| b = 0#u8 ↔ a = 0#u8 ∧ b = 0#u8 := by
  rw [U8.eq_equiv_bv_eq, U8.eq_equiv_bv_eq, U8.eq_equiv_bv_eq, UScalar.bv_or]
  exact BitVec.or_eq_zero_iff

theorem U128.or_eq_zero_no_simp (a b : U128) : a ||| b = 0#u128 ↔ a = 0#u128 ∧ b = 0#u128 := by
  rw [U128.eq_equiv_bv_eq, U128.eq_equiv_bv_eq, U128.eq_equiv_bv_eq, UScalar.bv_or]
  exact BitVec.or_eq_zero_iff

-- Test: and_maxVal using bv_and_maxVal' (defined here for testing)
private theorem U8.bv_and_maxVal' (x : U8) : x.toBitVec &&& 255#8 = x.toBitVec := by bv_tac 8
private theorem U128.bv_and_maxVal' (x : U128) : x.toBitVec &&& 340282366920938463463374607431768211455#128 = x.toBitVec := by bv_tac 128

theorem U8.and_maxVal_via_bv (x : U8) : x &&& 255#u8 = x := by
  rw [U8.eq_equiv_bv_eq, UScalar.bv_and]; exact U8.bv_and_maxVal' x

theorem U128.and_maxVal_via_bv (x : U128) : x &&& 340282366920938463463374607431768211455#u128 = x := by
  rw [U128.eq_equiv_bv_eq, UScalar.bv_and]; exact U128.bv_and_maxVal' x

end Aeneas.Std
