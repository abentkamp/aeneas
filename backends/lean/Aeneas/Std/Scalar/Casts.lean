import Aeneas.Std.Scalar.Core
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab

/-!
# Casts: Definitions

The reference semantics are here: https://doc.rust-lang.org/reference/expressions/operator-expr.html#semantics
-/

class ScalarCast (α β : Type) where
  cast {α} (β) : α → β

attribute [step_pure_def] ScalarCast.cast

/- When casting from unsigned integers, we truncate or **zero**-extend the integer. -/
uuscalar @[step_pure_def] instance : ScalarCast «%S2» «%S1» where
  cast x :=
    -- This truncates the integer if the numBits is smaller
    .ofBitVec (x.toBitVec.zeroExtend %BitWidth1)

iuscalar @[step_pure_def] instance : ScalarCast «%S2» «%S1» where
  cast x :=
    .ofBitVec (x.toBitVec.zeroExtend %BitWidth1)

/- When casting from signed integers, we truncate or **sign**-extend. -/
uiscalar @[step_pure_def] instance : ScalarCast «%S2» «%S1» where
  cast x :=
    .ofBitVec (x.toBitVec.signExtend %BitWidth1)

iiscalar @[step_pure_def] instance : ScalarCast «%S2» «%S1» where
  cast x :=
    .ofBitVec (x.toBitVec.signExtend %BitWidth1)

section
    /-! Checking that the semantics of casts are correct by using the examples given by the Rust reference. -/

  local macro:max x:term:max noWs "i8" : term => `(I8.ofInt $x (by decide))
  local macro:max x:term:max noWs "i16" : term => `(I16.ofInt $x (by decide))
  local macro:max x:term:max noWs "i32" : term => `(I32.ofInt $x (by decide))
  local macro:max x:term:max noWs "u8" : term => `(U8.ofNat $x (by decide))
  local macro:max x:term:max noWs "u16" : term => `(U16.ofNat $x (by decide))

  /- Cast between integers of same size -/
  #assert ScalarCast.cast _ 42i8    = 42u8       -- assert_eq!(42i8 as u8, 42u8);
  #assert ScalarCast.cast _ (-1)i8  = 255u8      -- assert_eq!(-1i8 as u8, 255u8);
  #assert ScalarCast.cast _ 255u8   = (-1)i8     -- assert_eq!(255u8 as i8, -1i8);
  #assert ScalarCast.cast _ (-1)i16 = 65535u16   -- assert_eq!(-1i16 as u16, 65535u16);

  /- Cast from larger integer to smaller integer -/
  #assert ScalarCast.cast _ 42u16 = 42u8         -- assert_eq!(42u16 as u8, 42u8);
  #assert ScalarCast.cast _ 1234u16 = 210u8      -- assert_eq!(1234u16 as u8, 210u8);
  #assert ScalarCast.cast _ 0xabcdu16 = 0xcdu8   -- assert_eq!(0xabcdu16 as u8, 0xcdu8);

  #assert ScalarCast.cast _ (-42)i16 = (-42)i8   -- assert_eq!(-42i16 as i8, -42i8);
  #assert ScalarCast.cast _ 1234u16 = (-46)i8   -- assert_eq!(1234u16 as i8, -46i8);
  #assert ScalarCast.cast _ 0xabcdi32 = (-51)i8  -- assert_eq!(0xabcdi32 as i8, -51i8);

  /- Cast from a smaller integer to a larger integer -/
  #assert ScalarCast.cast _ 42i8 = 42i16 -- assert_eq!(42i8 as i16, 42i16);
  #assert ScalarCast.cast _ (-17)i8 = (-17)i16 -- assert_eq!(-17i8 as i16, -17i16);
  #assert ScalarCast.cast _ 0b1000_1010u8 = 0b0000_0000_1000_1010u16 -- assert_eq!(0b1000_1010u8 as u16, 0b0000_0000_1000_1010u16, "Zero-extend");
  #assert ScalarCast.cast _ 0b0000_1010i8 = 0b0000_0000_0000_1010i16 -- assert_eq!(0b0000_1010i8 as i16, 0b0000_0000_0000_1010i16, "Sign-extend 0");
  #assert (ScalarCast.cast I16 (ScalarCast.cast I8 0b1000_1010u8)) = ScalarCast.cast I16 0b1111_1111_1000_1010u16 -- assert_eq!(0b1000_1010u8 as i8 as i16, 0b1111_1111_1000_1010u16 as i16, "Sign-extend 1");

end

scalar instance : ScalarCast Bool «%S» where
  cast x := if x then .ofBitVec (1#%BitWidth) else .ofBitVec (0#%BitWidth)

/-!
# Casts: Theorems
-/

uuscalar
/-- This theorem allows us not to use bit-vectors when reasoning about casts, if there are no overflows -/
theorem «%S1».cast_'S2_inBounds_spec
  (x : «%S2») (h : x.toNat ≤ «%S1».max) :
  lift (ScalarCast.cast «%S1» x) ⦃ y => y.toNat = x.toNat ⦄ := by
  simp only [lift, ScalarCast.cast, BitVec.truncate_eq_setWidth, WP.spec_ok, toNat_ofBitVec]
  simp only [max, BitVec.toNat_setWidth] at *
  apply Nat.mod_eq_of_lt; scalar_tac

iuscalar
/-- This theorem allows us not to use bit-vectors when reasoning about casts, if there are no overflows -/
theorem «%S1».cast_'S2_inBounds_spec
  (x : «%S2») (h : x.toNat ≤ «%S1».max) :
  lift (ScalarCast.cast «%S1» x) ⦃ y => y.toInt = x.toNat ⦄ := by
    simp only [lift, ScalarCast.cast, BitVec.truncate_eq_setWidth, WP.spec_ok, toInt_ofBitVec]
    simp only [BitVec.toInt_setWidth, max] at *
    have := System.Platform.numBits_eq
    apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac

iiscalar
/-- This theorem allows us not to use bit-vectors when reasoning about casts, if there are no overflows -/
theorem «%S1».cast_'S2_inBounds_spec
  (x : «%S2») (h : «%S1».min ≤ x.toInt ∧ x.toInt ≤ «%S1».max) :
  lift (ScalarCast.cast «%S1» x) ⦃ y => y.toInt = x.toInt ⦄ := by
  simp only [lift, ScalarCast.cast, BitVec.signExtend, toBitVec_toInt_eq, WP.spec_ok, toInt_ofBitVec]
  simp only [min, max, BitVec.toInt_ofInt, numBits_eq] at *
  have := System.Platform.numBits_eq
  apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac

uiscalar
/-- This theorem allows us not to use bit-vectors when reasoning about casts, if there are no overflows -/
theorem «%S1».cast_'S2_inBounds_spec
  (x : «%S2») (h : 0 ≤ x.toInt ∧ x.toInt ≤ «%S1».max) :
  lift (ScalarCast.cast «%S1» x) ⦃ y => y.toNat = x.toInt ⦄ := by
    simp only [lift, ScalarCast.cast, BitVec.signExtend, «%S2».toBitVec_toInt_eq, WP.spec_ok]
    simp only [«%S2».toInt, toNat, UScalarTy.numBits]
    simp only [IScalarTy.I16_numBits_eq, I16.toBitVec_toInt_eq, toBitVec_ofBitVec,
      BitVec.toNat_ofInt, Nat.reducePow, Nat.cast_ofNat, Int.ofNat_toNat, max] at *
    rw [numBits_eq] at *
    rw [max_eq_left (by scalar_tac), Int.emod_eq_of_lt (by scalar_tac) (by scalar_tac)]
    try scalar_tac

uscalar @[simp, step_pure ScalarCast.cast «%S» b]
theorem «%S».cast_fromBool_toNat_eq (b : Bool) : (ScalarCast.cast «%S» b).toNat = b.toNat := by
  simp only [ScalarCast.cast]
  split <;> simp only [*] <;> simp

iscalar @[simp, step_pure ScalarCast.cast «%S» b]
theorem «%S».cast_fromBool_toInt_eq (b : Bool) : (ScalarCast.cast «%S» b).toInt = b.toInt := by
  simp only [ScalarCast.cast]
  have := System.Platform.numBits_pos
  split <;> simp only [toInt] <;> grind

uscalar @[scalar_tac ScalarCast.cast «%S» b]
theorem «%S».cast_fromBool_bound_eq (b : Bool) : (ScalarCast.cast «%S» b).toNat ≤ 1 := by
  simp only [ScalarCast.cast]
  split <;> simp only [toNat, *] <;> simp

uscalar @[simp]
theorem «%S».cast_fromBool_toBitVec_eq (b : Bool) :
    (ScalarCast.cast «%S» b).toBitVec = (BitVec.ofBool b).zeroExtend _ := by
  simp only [ScalarCast.cast, BitVec.truncate_eq_setWidth]
  cases b <;> simp <;> grind

iscalar @[simp]
theorem «%S».cast_fromBool_toBitVec_eq (b : Bool) :
    (ScalarCast.cast «%S» b).toBitVec = (BitVec.ofBool b).zeroExtend _ := by
  simp only [ScalarCast.cast, BitVec.truncate_eq_setWidth]
  cases b <;> simp <;> grind

iscalar @[scalar_tac ScalarCast.cast «%S» b]
theorem «%S».cast_fromBool_bound_eq (b : Bool) :
  0 ≤ (ScalarCast.cast «%S» b).toInt ∧ (ScalarCast.cast «%S» b).toInt ≤ 1 := by
  simp only [ScalarCast.cast]
  split <;> simp only [toInt]
  · have : (1#%BitWidth).toInt = 1 := by
      simp [BitVec.toInt]
      try cases System.Platform.numBits_eq <;> simp [*]
    simp [this]
  · simp

uuscalar theorem «%S1».cast_'S2_toNat_eq_mod (x : «%S1») :
  (ScalarCast.cast «%S2» x).toNat = x.toNat % 2^%BitWidth2 := by
  simp only [ScalarCast.cast, toNat]
  simp only [UScalarTy.numBits]
  simp only [BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, toBitVec_toNat, «%S2».toNat_ofBitVec]


-- TODO: factor our the casts

@[simp, scalar_tac_simps, simp_scalar_safe]
theorem U8.cast_U16_toNat_eq (x : U8) : (ScalarCast.cast U16 x).toNat = x.toNat := by
  simp [cast_U16_toNat_eq_mod]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_safe]
theorem U8.cast_U32_toNat_eq (x : U8) : (ScalarCast.cast U32 x).toNat = x.toNat := by
  simp [cast_U32_toNat_eq_mod]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_safe]
theorem U8.cast_U64_toNat_eq (x : U8) : (ScalarCast.cast U64 x).toNat = x.toNat := by
  simp [cast_U64_toNat_eq_mod]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_safe]
theorem U8.cast_U128_toNat_eq (x : U8) : (ScalarCast.cast U128 x).toNat = x.toNat := by
  simp [cast_U128_toNat_eq_mod]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_safe]
theorem U8.cast_Usize_toNat_eq (x : U8) : (ScalarCast.cast Usize x).toNat = x.toNat := by
  simp [cast_Usize_toNat_eq_mod]; cases System.Platform.numBits_eq <;> simp [*] <;> scalar_tac

@[simp, scalar_tac_simps, simp_scalar_safe]
theorem U16.cast_U32_toNat_eq (x : U16) : (ScalarCast.cast U32 x).toNat = x.toNat := by
  simp [cast_U32_toNat_eq_mod]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_safe]
theorem U16.cast_U64_toNat_eq (x : U16) : (ScalarCast.cast U64 x).toNat = x.toNat := by
  simp [cast_U64_toNat_eq_mod]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_safe]
theorem U16.cast_U128_toNat_eq (x : U16) : (ScalarCast.cast U128 x).toNat = x.toNat := by
  simp [cast_U128_toNat_eq_mod]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_safe]
theorem U16.cast_Usize_toNat_eq (x : U16) : (ScalarCast.cast Usize x).toNat = x.toNat := by
  simp [cast_Usize_toNat_eq_mod]; cases System.Platform.numBits_eq <;> simp [*] <;> scalar_tac

@[simp, scalar_tac_simps, simp_scalar_safe]
theorem U32.cast_U64_toNat_eq (x : U32) : (ScalarCast.cast U64 x).toNat = x.toNat := by
  simp [cast_U64_toNat_eq_mod]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_safe]
theorem U32.cast_U128_toNat_eq (x : U32) : (ScalarCast.cast U128 x).toNat = x.toNat := by
  simp [cast_U128_toNat_eq_mod]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_safe]
theorem U32.cast_Usize_toNat_eq (x : U32) : (ScalarCast.cast Usize x).toNat = x.toNat := by
  simp [cast_Usize_toNat_eq_mod]; cases System.Platform.numBits_eq <;> simp [*] <;> scalar_tac

@[simp, scalar_tac_simps, simp_scalar_safe]
theorem U64.cast_U128_toNat_eq (x : U64) : (ScalarCast.cast U128 x).toNat = x.toNat := by
  simp [cast_U128_toNat_eq_mod]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_safe]
theorem U64.cast_Usize_toNat_eq (x : U64) (h : System.Platform.numBits = 64) :
    (ScalarCast.cast Usize x).toNat = x.toNat := by
  simp [cast_Usize_toNat_eq_mod]; scalar_tac

uuscalar @[simp]
theorem «%S2».cast_'S1_toNat_mod_pow_of_inBounds_eq
  (x : «%S2») (h : x.toNat < 2^%BitWidth1) :
  (ScalarCast.cast «%S1» x).toNat = x.toNat := by
  simp [cast_U8_toNat_eq_mod, cast_U16_toNat_eq_mod, cast_U32_toNat_eq_mod,
    cast_U64_toNat_eq_mod, cast_U128_toNat_eq_mod, cast_Usize_toNat_eq_mod]
  try cases System.Platform.numBits_eq <;> scalar_tac

uuscalar @[simp]
theorem «%S2».cast_'S1_toBitVec_eq (x : «%S2») :
  (ScalarCast.cast «%S1» x).toBitVec = x.toBitVec.setWidth %BitWidth1 := by
  simp [ScalarCast.cast]

example (x : U16) : (ScalarCast.cast U32 x).toNat = x.toNat := by simp
example : (ScalarCast.cast U16 (U32.ofNat 42)).toNat = 42 := by simp

iiscalar theorem «%S1».cast_'S2_toInt_eq (x : «%S1») :
  (ScalarCast.cast «%S2» x).toInt = Int.bmod x.toInt
  (2^(Min.min «%S2».numBits «%S1».numBits)) := by
    simp only [ScalarCast.cast, toInt, «%S1».numBits_eq, «%S2».numBits_eq]
    simp only [IScalarTy.numBits, BitVec.toInt_signExtend, «%S2».toInt_ofBitVec,
      «%S2».toBitVec_ofBitVec]

iiscalar @[simp] theorem «%S2».cast_'S1_toInt_mod_pow_greater_numBits
  (x : «%S2») (h : «%S2».numBits ≤ «%S1».numBits) :
  (ScalarCast.cast «%S1» x).toInt = x.toInt := by
  simp [cast_I8_toInt_eq, cast_I16_toInt_eq, cast_I32_toInt_eq,
    cast_I64_toInt_eq, cast_I128_toInt_eq, cast_Isize_toInt_eq]
  have hBounds := x.hBounds
  try simp [h]
  have := System.Platform.numBits_pos
  have : numBits = numBits - 1 + 1 := by rw [numBits_eq] <;> omega
  rw [this]
  apply Int.bmod_pow2_eq_of_inBounds <;> omega

iiscalar @[simp]
theorem «%S1».cast_'S2_toInt_mod_pow_inBounds (x : «%S1»)
  (hMin : -2^(«%S2».numBits - 1) ≤ x.toInt) (hMax : x.toInt < 2^(«%S2».numBits - 1)) :
  (ScalarCast.cast «%S2» x).toInt = x.toInt := by
  simp only [cast_'S2_toInt_eq]
  rw [Int.bmod_eq_of_le_mul_two]
  by_cases h : «%S2».numBits ≤ numBits
  · rw [Nat.min_eq_left h]
    have : -((2 : Int) ^ («%S2».numBits - 1) * 2) ≤ ↑x * 2 := by omega
    rwa [pow_sub_one_mul «%S2».numBits_nonzero] at this
  · rw [Nat.min_eq_right (by omega)]
    have := x.hBounds.1
    have : -((2 : Int) ^ (numBits - 1) * 2) ≤ ↑x * 2 := by scalar_tac
    rwa [pow_sub_one_mul numBits_nonzero] at this
  by_cases h : «%S2».numBits ≤ numBits
  · rw [Nat.min_eq_left h]
    have : ↑x * 2 < ((2 : Int) ^ («%S2».numBits - 1) * 2) := by omega
    rwa [pow_sub_one_mul «%S2».numBits_nonzero] at this
  · rw [Nat.min_eq_right (by omega)]
    have := x.hBounds.1
    have : ↑x * 2 < ((2 : Int) ^ (numBits - 1) * 2) := by scalar_tac
    rwa [pow_sub_one_mul numBits_nonzero] at this

end Aeneas.Std
