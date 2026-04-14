import Aeneas.Tactic.Solver.BvTac.BvTac

/-!
# Bitwise identity lemmas for scalar types

`x &&& maxVal = x` and `maxVal &&& x = x` at the scalar, `.toNat` (Nat), and `.toBitVec` (BitVec) levels
for each unsigned scalar type.
-/

namespace Aeneas.Std

open Aeneas.Std

-- ============================================================================
-- x.toBitVec &&& maxVal = x.toBitVec  (BitVec level)
-- ============================================================================

@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U8.bv_and_maxVal (x : U8) : x.toBitVec &&& 255#8 = x.toBitVec := by bv_tac 8
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U16.bv_and_maxVal (x : U16) : x.toBitVec &&& 65535#16 = x.toBitVec := by bv_tac 16
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U32.bv_and_maxVal (x : U32) : x.toBitVec &&& 4294967295#32 = x.toBitVec := by bv_tac 32
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U64.bv_and_maxVal (x : U64) : x.toBitVec &&& 18446744073709551615#64 = x.toBitVec := by bv_tac 64
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U128.bv_and_maxVal (x : U128) : x.toBitVec &&& 340282366920938463463374607431768211455#128 = x.toBitVec := by bv_tac 128

-- ============================================================================
-- maxVal &&& x.toBitVec = x.toBitVec  (BitVec level)
-- ============================================================================

@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U8.bv_maxVal_and (x : U8) : 255#8 &&& x.toBitVec = x.toBitVec := by bv_tac 8
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U16.bv_maxVal_and (x : U16) : 65535#16 &&& x.toBitVec = x.toBitVec := by bv_tac 16
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U32.bv_maxVal_and (x : U32) : 4294967295#32 &&& x.toBitVec = x.toBitVec := by bv_tac 32
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U64.bv_maxVal_and (x : U64) : 18446744073709551615#64 &&& x.toBitVec = x.toBitVec := by bv_tac 64
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U128.bv_maxVal_and (x : U128) : 340282366920938463463374607431768211455#128 &&& x.toBitVec = x.toBitVec := by bv_tac 128

-- ============================================================================
-- x &&& maxVal = x  (scalar level)
-- ============================================================================

@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U8.and_maxVal (x : U8) : x &&& 255#u8 = x := by
  rw [U8.eq_equiv_bv_eq, UScalar.bv_and]; exact U8.bv_and_maxVal x
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U16.and_maxVal (x : U16) : x &&& 65535#u16 = x := by
  rw [U16.eq_equiv_bv_eq, UScalar.bv_and]; exact U16.bv_and_maxVal x
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U32.and_maxVal (x : U32) : x &&& 4294967295#u32 = x := by
  rw [U32.eq_equiv_bv_eq, UScalar.bv_and]; exact U32.bv_and_maxVal x
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U64.and_maxVal (x : U64) : x &&& 18446744073709551615#u64 = x := by
  rw [U64.eq_equiv_bv_eq, UScalar.bv_and]; exact U64.bv_and_maxVal x
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U128.and_maxVal (x : U128) : x &&& 340282366920938463463374607431768211455#u128 = x := by
  rw [U128.eq_equiv_bv_eq, UScalar.bv_and]; exact U128.bv_and_maxVal x

-- ============================================================================
-- maxVal &&& x = x  (scalar level)
-- ============================================================================

@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U8.maxVal_and (x : U8) : 255#u8 &&& x = x := by
  rw [U8.eq_equiv_bv_eq, UScalar.bv_and]; exact U8.bv_maxVal_and x
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U16.maxVal_and (x : U16) : 65535#u16 &&& x = x := by
  rw [U16.eq_equiv_bv_eq, UScalar.bv_and]; exact U16.bv_maxVal_and x
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U32.maxVal_and (x : U32) : 4294967295#u32 &&& x = x := by
  rw [U32.eq_equiv_bv_eq, UScalar.bv_and]; exact U32.bv_maxVal_and x
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U64.maxVal_and (x : U64) : 18446744073709551615#u64 &&& x = x := by
  rw [U64.eq_equiv_bv_eq, UScalar.bv_and]; exact U64.bv_maxVal_and x
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U128.maxVal_and (x : U128) : 340282366920938463463374607431768211455#u128 &&& x = x := by
  rw [U128.eq_equiv_bv_eq, UScalar.bv_and]; exact U128.bv_maxVal_and x

-- ============================================================================
-- x.toNat &&& maxVal = x.toNat  (Nat level)
-- ============================================================================

@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U8.val_and_maxVal (x : U8) : x.toNat &&& 255 = x.toNat := by
  have h := congrArg UScalar.toNat (U8.and_maxVal x); simp only [UScalar.val_and] at h; exact h
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U16.val_and_maxVal (x : U16) : x.toNat &&& 65535 = x.toNat := by
  have h := congrArg UScalar.toNat (U16.and_maxVal x); simp only [UScalar.val_and] at h; exact h
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U32.val_and_maxVal (x : U32) : x.toNat &&& 4294967295 = x.toNat := by
  have h := congrArg UScalar.toNat (U32.and_maxVal x); simp only [UScalar.val_and] at h; exact h
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U64.val_and_maxVal (x : U64) : x.toNat &&& 18446744073709551615 = x.toNat := by
  have h := congrArg UScalar.toNat (U64.and_maxVal x); simp only [UScalar.val_and] at h; exact h
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U128.val_and_maxVal (x : U128) : x.toNat &&& 340282366920938463463374607431768211455 = x.toNat := by
  have h := congrArg UScalar.toNat (U128.and_maxVal x); simp only [UScalar.val_and] at h; exact h

-- ============================================================================
-- maxVal &&& x.toNat = x.toNat  (Nat level)
-- ============================================================================

@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U8.maxVal_and_val (x : U8) : 255 &&& x.toNat = x.toNat := by
  have h := congrArg UScalar.toNat (U8.maxVal_and x); simp only [UScalar.val_and] at h; exact h
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U16.maxVal_and_val (x : U16) : 65535 &&& x.toNat = x.toNat := by
  have h := congrArg UScalar.toNat (U16.maxVal_and x); simp only [UScalar.val_and] at h; exact h
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U32.maxVal_and_val (x : U32) : 4294967295 &&& x.toNat = x.toNat := by
  have h := congrArg UScalar.toNat (U32.maxVal_and x); simp only [UScalar.val_and] at h; exact h
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U64.maxVal_and_val (x : U64) : 18446744073709551615 &&& x.toNat = x.toNat := by
  have h := congrArg UScalar.toNat (U64.maxVal_and x); simp only [UScalar.val_and] at h; exact h
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U128.maxVal_and_val (x : U128) : 340282366920938463463374607431768211455 &&& x.toNat = x.toNat := by
  have h := congrArg UScalar.toNat (U128.maxVal_and x); simp only [UScalar.val_and] at h; exact h

-- ============================================================================
-- x.toBitVec % (2^n)#n = x.toBitVec  (BitVec level)
-- ============================================================================

@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U8.bv_mod_size (x : U8) : x.toBitVec % 256#8 = x.toBitVec := by bv_tac 8
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U16.bv_mod_size (x : U16) : x.toBitVec % 65536#16 = x.toBitVec := by bv_tac 16
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U32.bv_mod_size (x : U32) : x.toBitVec % 4294967296#32 = x.toBitVec := by bv_tac 32
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U64.bv_mod_size (x : U64) : x.toBitVec % 18446744073709551616#64 = x.toBitVec := by bv_tac 64
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U128.bv_mod_size (x : U128) : x.toBitVec % 340282366920938463463374607431768211456#128 = x.toBitVec := by bv_tac 128

-- ============================================================================
-- x.toNat % (2^n) = x.toNat  (Nat level)
-- ============================================================================

@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U8.val_mod_size (x : U8) : x.toNat % 256 = x.toNat := Nat.mod_eq_of_lt (by scalar_tac)
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U16.val_mod_size (x : U16) : x.toNat % 65536 = x.toNat := Nat.mod_eq_of_lt (by scalar_tac)
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U32.val_mod_size (x : U32) : x.toNat % 4294967296 = x.toNat := Nat.mod_eq_of_lt (by scalar_tac)
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U64.val_mod_size (x : U64) : x.toNat % 18446744073709551616 = x.toNat := Nat.mod_eq_of_lt (by scalar_tac)
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U128.val_mod_size (x : U128) : x.toNat % 340282366920938463463374607431768211456 = x.toNat := Nat.mod_eq_of_lt (by scalar_tac)

-- ============================================================================
-- x &&& 0 = 0  (scalar level)
-- ============================================================================

@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U8.and_zero (x : U8) : x &&& 0#u8 = 0#u8 := by
  rw [U8.eq_equiv_bv_eq, UScalar.bv_and]; exact BitVec.and_zero
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U16.and_zero (x : U16) : x &&& 0#u16 = 0#u16 := by
  rw [U16.eq_equiv_bv_eq, UScalar.bv_and]; exact BitVec.and_zero
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U32.and_zero (x : U32) : x &&& 0#u32 = 0#u32 := by
  rw [U32.eq_equiv_bv_eq, UScalar.bv_and]; exact BitVec.and_zero
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U64.and_zero (x : U64) : x &&& 0#u64 = 0#u64 := by
  rw [U64.eq_equiv_bv_eq, UScalar.bv_and]; exact BitVec.and_zero
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U128.and_zero (x : U128) : x &&& 0#u128 = 0#u128 := by
  rw [U128.eq_equiv_bv_eq, UScalar.bv_and]; exact BitVec.and_zero

-- 0 &&& x = 0
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U8.zero_and (x : U8) : 0#u8 &&& x = 0#u8 := by
  rw [U8.eq_equiv_bv_eq, UScalar.bv_and]; exact BitVec.zero_and
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U16.zero_and (x : U16) : 0#u16 &&& x = 0#u16 := by
  rw [U16.eq_equiv_bv_eq, UScalar.bv_and]; exact BitVec.zero_and
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U32.zero_and (x : U32) : 0#u32 &&& x = 0#u32 := by
  rw [U32.eq_equiv_bv_eq, UScalar.bv_and]; exact BitVec.zero_and
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U64.zero_and (x : U64) : 0#u64 &&& x = 0#u64 := by
  rw [U64.eq_equiv_bv_eq, UScalar.bv_and]; exact BitVec.zero_and
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U128.zero_and (x : U128) : 0#u128 &&& x = 0#u128 := by
  rw [U128.eq_equiv_bv_eq, UScalar.bv_and]; exact BitVec.zero_and

-- ============================================================================
-- x ||| 0 = x  (scalar level)
-- ============================================================================

@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U8.or_zero (x : U8) : x ||| 0#u8 = x := by
  rw [U8.eq_equiv_bv_eq, UScalar.bv_or]; exact BitVec.or_zero
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U16.or_zero (x : U16) : x ||| 0#u16 = x := by
  rw [U16.eq_equiv_bv_eq, UScalar.bv_or]; exact BitVec.or_zero
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U32.or_zero (x : U32) : x ||| 0#u32 = x := by
  rw [U32.eq_equiv_bv_eq, UScalar.bv_or]; exact BitVec.or_zero
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U64.or_zero (x : U64) : x ||| 0#u64 = x := by
  rw [U64.eq_equiv_bv_eq, UScalar.bv_or]; exact BitVec.or_zero
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U128.or_zero (x : U128) : x ||| 0#u128 = x := by
  rw [U128.eq_equiv_bv_eq, UScalar.bv_or]; exact BitVec.or_zero

-- 0 ||| x = x
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U8.zero_or (x : U8) : 0#u8 ||| x = x := by
  rw [U8.eq_equiv_bv_eq, UScalar.bv_or]; exact BitVec.zero_or
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U16.zero_or (x : U16) : 0#u16 ||| x = x := by
  rw [U16.eq_equiv_bv_eq, UScalar.bv_or]; exact BitVec.zero_or
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U32.zero_or (x : U32) : 0#u32 ||| x = x := by
  rw [U32.eq_equiv_bv_eq, UScalar.bv_or]; exact BitVec.zero_or
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U64.zero_or (x : U64) : 0#u64 ||| x = x := by
  rw [U64.eq_equiv_bv_eq, UScalar.bv_or]; exact BitVec.zero_or
@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem U128.zero_or (x : U128) : 0#u128 ||| x = x := by
  rw [U128.eq_equiv_bv_eq, UScalar.bv_or]; exact BitVec.zero_or

-- ============================================================================
-- a ^^^ b = 0 ↔ a = b  (scalar level)
-- ============================================================================

@[simp, simp_scalar_safe, grind =, agrind =]
theorem U8.xor_eq_zero_iff (a b : U8) : a ^^^ b = 0#u8 ↔ a = b := by
  rw [U8.eq_equiv_bv_eq, U8.eq_equiv_bv_eq, UScalar.bv_xor]; exact BitVec.xor_eq_zero_iff
@[simp, simp_scalar_safe, grind =, agrind =]
theorem U16.xor_eq_zero_iff (a b : U16) : a ^^^ b = 0#u16 ↔ a = b := by
  rw [U16.eq_equiv_bv_eq, U16.eq_equiv_bv_eq, UScalar.bv_xor]; exact BitVec.xor_eq_zero_iff
@[simp, simp_scalar_safe, grind =, agrind =]
theorem U32.xor_eq_zero_iff (a b : U32) : a ^^^ b = 0#u32 ↔ a = b := by
  rw [U32.eq_equiv_bv_eq, U32.eq_equiv_bv_eq, UScalar.bv_xor]; exact BitVec.xor_eq_zero_iff
@[simp, simp_scalar_safe, grind =, agrind =]
theorem U64.xor_eq_zero_iff (a b : U64) : a ^^^ b = 0#u64 ↔ a = b := by
  rw [U64.eq_equiv_bv_eq, U64.eq_equiv_bv_eq, UScalar.bv_xor]; exact BitVec.xor_eq_zero_iff
@[simp, simp_scalar_safe, grind =, agrind =]
theorem U128.xor_eq_zero_iff (a b : U128) : a ^^^ b = 0#u128 ↔ a = b := by
  rw [U128.eq_equiv_bv_eq, U128.eq_equiv_bv_eq, UScalar.bv_xor]; exact BitVec.xor_eq_zero_iff

-- ============================================================================
-- a ||| b = 0 ↔ a = 0 ∧ b = 0  (scalar level)
-- ============================================================================

@[simp, simp_scalar_safe, grind =, agrind =]
theorem U8.or_eq_zero_iff (a b : U8) : a ||| b = 0#u8 ↔ a = 0#u8 ∧ b = 0#u8 := by
  rw [U8.eq_equiv_bv_eq, U8.eq_equiv_bv_eq, U8.eq_equiv_bv_eq, UScalar.bv_or]
  exact BitVec.or_eq_zero_iff
@[simp, simp_scalar_safe, grind =, agrind =]
theorem U16.or_eq_zero_iff (a b : U16) : a ||| b = 0#u16 ↔ a = 0#u16 ∧ b = 0#u16 := by
  rw [U16.eq_equiv_bv_eq, U16.eq_equiv_bv_eq, U16.eq_equiv_bv_eq, UScalar.bv_or]
  exact BitVec.or_eq_zero_iff
@[simp, simp_scalar_safe, grind =, agrind =]
theorem U32.or_eq_zero_iff (a b : U32) : a ||| b = 0#u32 ↔ a = 0#u32 ∧ b = 0#u32 := by
  rw [U32.eq_equiv_bv_eq, U32.eq_equiv_bv_eq, U32.eq_equiv_bv_eq, UScalar.bv_or]
  exact BitVec.or_eq_zero_iff
@[simp, simp_scalar_safe, grind =, agrind =]
theorem U64.or_eq_zero_iff (a b : U64) : a ||| b = 0#u64 ↔ a = 0#u64 ∧ b = 0#u64 := by
  rw [U64.eq_equiv_bv_eq, U64.eq_equiv_bv_eq, U64.eq_equiv_bv_eq, UScalar.bv_or]
  exact BitVec.or_eq_zero_iff
@[simp, simp_scalar_safe, grind =, agrind =]
theorem U128.or_eq_zero_iff (a b : U128) : a ||| b = 0#u128 ↔ a = 0#u128 ∧ b = 0#u128 := by
  rw [U128.eq_equiv_bv_eq, U128.eq_equiv_bv_eq, U128.eq_equiv_bv_eq, UScalar.bv_or]
  exact BitVec.or_eq_zero_iff

end Aeneas.Std
