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

open Lean in
set_option hygiene false in
run_cmd do
 for ty in [`U8, `U16, `U32, `U64, `U128, `Usize] do
    /- When casting from unsigned integers, we truncate or **zero**-extend the integer. -/
    Lean.Elab.Command.elabCommand (← `(
      scalar @[step_pure_def] instance : ScalarCast $(mkIdent ty) «%S» where
        cast x :=
          -- This truncates the integer if the numBits is smaller
          ⟨ x.toBitVec.zeroExtend %BitWidth ⟩
    ))

open Lean in
set_option hygiene false in
run_cmd do
 for ty in [`I8, `I16, `I32, `I64, `I128, `Isize] do
    /- When casting from signed integers, we truncate or **sign**-extend. -/
    Lean.Elab.Command.elabCommand (← `(
      scalar @[step_pure_def] instance : ScalarCast $(mkIdent ty) «%S» where
        cast x :=
          ⟨ x.toBitVec.signExtend %BitWidth ⟩
    ))

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
  cast x := if x then ⟨ 1#%BitWidth ⟩ else ⟨ 0#%BitWidth ⟩

/-!
# Casts: Theorems
-/

/- This theorem allows us not to use bit-vectors when reasoning about casts, if there are no overflows -/
open Lean in
set_option hygiene false in
run_cmd do
  for ty in [`U8, `U16, `U32, `U64, `U128, `Usize] do
    Lean.Elab.Command.elabCommand (← `(
      uscalar theorem $(mkIdent s!"«%S».cast_{ty.toString}_inBounds_spec".toName)
        (x : $(mkIdent ty)) (h : x.toNat ≤ «%S».max) :
        lift (ScalarCast.cast «%S» x) ⦃ y => y.toNat = x.toNat ⦄ := by
        simp only [lift, ScalarCast.cast, BitVec.truncate_eq_setWidth, WP.spec_ok, UScalar.toNat]
        unfold UScalarTy.numBits
        simp only [max, BitVec.toNat_setWidth] at *
        apply Nat.mod_eq_of_lt; scalar_tac
    ))

/- This theorem allows us not to use bit-vectors when reasoning about casts, if there are no overflows -/
open Lean in
set_option hygiene false in
run_cmd do
  for ty in [`U8, `U16, `U32, `U64, `U128, `Usize] do
    Lean.Elab.Command.elabCommand (← `(
      iscalar theorem $(mkIdent s!"«%S».cast_{ty.toString}_inBounds_spec".toName)
        (x : $(mkIdent ty)) (h : x.toNat ≤ «%S».max) :
        lift (ScalarCast.cast «%S» x) ⦃ y => y.toInt = x.toNat ⦄ := by
          simp only [lift, ScalarCast.cast, BitVec.truncate_eq_setWidth, WP.spec_ok]
          simp only [IScalar.toInt, UScalar.toNat]
          simp only [IScalarTy.numBits]
          simp only [BitVec.toInt_setWidth, UScalar.toBitVec_toNat] at *
          have := System.Platform.numBits_eq
          apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac
    ))

/- This theorem allows us not to use bit-vectors when reasoning about casts, if there are no overflows -/
open Lean in
set_option hygiene false in
run_cmd do
  for ty in [`I8, `I16, `I32, `I64, `I128, `Isize] do
    Lean.Elab.Command.elabCommand (← `(
      iscalar theorem $(mkIdent s!"«%S».cast_{ty.toString}_inBounds_spec".toName)
      (x : $(mkIdent ty)) (h : «%S».min ≤ x.toInt ∧ x.toInt ≤ «%S».max) :
        lift (ScalarCast.cast «%S» x) ⦃ y => y.toInt = x.toInt ⦄
        := by
        simp only [lift, ScalarCast.cast, BitVec.signExtend, IScalar.toBitVec_toInt_eq, WP.spec_ok]
        simp only [IScalar.toInt]
        simp only [IScalarTy.numBits]
        simp only [min, max, IScalar.toBitVec_toInt_eq, BitVec.toInt_ofInt] at *
        have := System.Platform.numBits_eq
        apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac
    ))

/- This theorem allows us not to use bit-vectors when reasoning about casts, if there are no overflows -/
open Lean in
set_option hygiene false in
run_cmd do
  for ty in [`I8, `I16, `I32, `I64, `I128, `Isize] do
    Lean.Elab.Command.elabCommand (← `(
      uscalar theorem $(mkIdent s!"«%S».cast_{ty.toString}_inBounds_spec".toName)
        (x : $(mkIdent ty)) (h : 0 ≤ x.toInt ∧ x.toInt ≤ U8.max) :
        lift (ScalarCast.cast U8 x) ⦃ y => y.toNat = x.toInt ⦄ := by
        simp only [lift, ScalarCast.cast, BitVec.signExtend, IScalar.toBitVec_toInt_eq, WP.spec_ok]
        simp only [IScalar.toInt, UScalar.toNat]
        simp only [UScalarTy.numBits]
        simp only [Nat.cast_pow, Nat.cast_ofNat,
          IScalar.toBitVec_toInt_eq, BitVec.toNat_ofInt, Int.ofNat_toNat] at *
        scalar_tac
    ))

uscalar @[simp, step_pure ScalarCast.cast «%S» b]
theorem «%S».cast_fromBool_toNat_eq (b : Bool) : (ScalarCast.cast «%S» b).toNat = b.toNat := by
  simp only [ScalarCast.cast]
  split <;> simp only [UScalar.toNat, *] <;> simp

iscalar @[simp, step_pure ScalarCast.cast «%S» b]
theorem «%S».cast_fromBool_toInt_eq (b : Bool) : (ScalarCast.cast «%S» b).toInt = b.toInt := by
  simp only [ScalarCast.cast]
  have := System.Platform.numBits_pos
  split <;> simp only [IScalar.toInt] <;> grind

uscalar @[scalar_tac ScalarCast.cast «%S» b]
theorem «%S».cast_fromBool_bound_eq (b : Bool) : (ScalarCast.cast «%S» b).toNat ≤ 1 := by
  simp only [ScalarCast.cast]
  split <;> simp only [UScalar.toNat, *] <;> simp

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
  split <;> simp only [IScalar.toInt]
  · have : (1#%BitWidth).toInt = 1 := by
      simp [BitVec.toInt]
      try cases System.Platform.numBits_eq <;> simp [*]
    simp [this]
  · simp

open Lean in
set_option hygiene false in
run_cmd do
  for ty in [`U8, `U16, `U32, `U64, `U128, `Usize] do
    Lean.Elab.Command.elabCommand (← `(
      uscalar theorem $(mkIdent s!"{ty.toString}.cast_'S_toNat_eq_mod".toName) (x : $(mkIdent ty)) :
        (ScalarCast.cast «%S» x).toNat = x.toNat % 2^%BitWidth := by
        simp only [ScalarCast.cast, UScalar.toNat]
        simp only [UScalarTy.numBits]
        simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, toBitVec_toNat]
    ))

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

open Lean in
set_option hygiene false in
run_cmd do
  for ty in [`U8, `U16, `U32, `U64, `U128, `Usize] do
    Lean.Elab.Command.elabCommand (← `(
      uscalar @[simp]
      theorem $(mkIdent s!"{ty.toString}.cast_'S_toNat_mod_pow_of_inBounds_eq".toName)
        (x : $(mkIdent ty)) (h : x.toNat < 2^%BitWidth) :
        (ScalarCast.cast «%S» x).toNat = x.toNat := by
        simp [cast_U8_toNat_eq_mod, cast_U16_toNat_eq_mod, cast_U32_toNat_eq_mod,
          cast_U64_toNat_eq_mod, cast_U128_toNat_eq_mod, cast_Usize_toNat_eq_mod]
        try cases System.Platform.numBits_eq <;> scalar_tac
    ))

open Lean in
set_option hygiene false in
run_cmd do
  for ty in [`U8, `U16, `U32, `U64, `U128, `Usize] do
    Lean.Elab.Command.elabCommand (← `(
      uscalar @[simp]
      theorem $(mkIdent s!"{ty.toString}.cast_'S_toBitVec_eq".toName) (x : $(mkIdent ty)) :
        (ScalarCast.cast «%S» x).toBitVec = x.toBitVec.setWidth %BitWidth := by
        simp [ScalarCast.cast]
    ))

example (x : U16) : (ScalarCast.cast U32 x).toNat = x.toNat := by simp
example : (ScalarCast.cast U16 (U32.ofNat 42)).toNat = 42 := by simp

open Lean in
set_option hygiene false in
run_cmd do
  for ty1 in [`I8, `I16, `I32, `I64, `I128, `Isize] do
    for ty2 in [`I8, `I16, `I32, `I64, `I128, `Isize] do
      Lean.Elab.Command.elabCommand (← `(
        theorem $(mkIdent s!"{ty1.toString}.cast_{ty2.toString}_toInt_eq".toName) (x : $(mkIdent ty1)) :
          (ScalarCast.cast $(mkIdent ty2) x).toInt = Int.bmod x.toInt
            (2^(Min.min  $(mkIdent (ty2 ++ `numBits)) $(mkIdent (ty1 ++ `numBits)))) := by
          simp only [ScalarCast.cast, IScalar.toInt, I8.numBits_eq, I16.numBits_eq,
            I32.numBits_eq, I64.numBits_eq, I128.numBits_eq, Isize.numBits_eq]
          simp only [IScalarTy.numBits, BitVec.toInt_signExtend]
      ))

open Lean in
set_option hygiene false in
run_cmd do
  for ty1 in [`I8, `I16, `I32, `I64, `I128, `Isize] do
    for ty2 in [`I8, `I16, `I32, `I64, `I128, `Isize] do
      Lean.Elab.Command.elabCommand (← `(
        @[simp] theorem $(mkIdent s!"{ty1.toString}.cast_{ty2.toString}_toInt_mod_pow_greater_numBits".toName)
          (x : $(mkIdent ty1)) (h : $(mkIdent (ty1 ++ `numBits)) ≤ $(mkIdent (ty2 ++ `numBits))) :
          (ScalarCast.cast $(mkIdent ty2) x).toInt = x.toInt := by
          simp [cast_I8_toInt_eq, cast_I16_toInt_eq, cast_I32_toInt_eq,
            cast_I64_toInt_eq, cast_I128_toInt_eq, cast_Isize_toInt_eq]
          have hBounds := x.hBounds
          try simp [h]
          have := System.Platform.numBits_pos
          have : numBits = numBits - 1 + 1 := by rw [numBits_eq] <;> omega
          rw [this]
          apply Int.bmod_pow2_eq_of_inBounds <;> omega
      ))

open Lean in
set_option hygiene false in
run_cmd do
  for ty1 in [`I8, `I16, `I32, `I64, `I128, `Isize] do
    for ty2 in [`I8, `I16, `I32, `I64, `I128, `Isize] do
      Lean.Elab.Command.elabCommand (← `(
        @[simp]
        theorem $(mkIdent s!"{ty1.toString}.cast_{ty2.toString}_toInt_mod_pow_inBounds".toName)
          (x : $(mkIdent ty1))
          (hMin : -2^($(mkIdent (ty2 ++ `numBits)) - 1) ≤ x.toInt) (hMax : x.toInt < 2^($(mkIdent (ty2 ++ `numBits)) - 1)) :
          (ScalarCast.cast $(mkIdent ty2) x).toInt = x.toInt := by sorry
      ))

-- theorem I8.ss
--   (x : I8)
--   (hMin : -2^(I16.numBits - 1) ≤ x.toInt) (hMax : x.toInt < 2^(I16.numBits - 1)) :
--   (ScalarCast.cast I16 x).toInt = x.toInt := by
--   simp only [cast_I8_toInt_eq, cast_I16_toInt_eq, cast_I32_toInt_eq,
--     cast_I64_toInt_eq, cast_I128_toInt_eq, cast_Isize_toInt_eq]
--   rw [Int.bmod_eq_of_le_mul_two]
--   by_cases h : I16.numBits ≤ numBits
--   · rw [Nat.min_eq_left h]
--     have : -((2 : Int) ^ (I16.numBits - 1) * 2) ≤ ↑x * 2 := by grind
--     rwa [pow_sub_one_mul I16.numBits_nonzero] at this
--   · rw [Nat.min_eq_right (by grind)]
--     have := (IScalar.hBounds x).1
--     have : -((2 : Int) ^ (numBits - 1) * 2) ≤ ↑x * 2 := by grind [numBits_eq]
--     rwa [pow_sub_one_mul numBits_nonzero] at this
--   by_cases h : I16.numBits ≤ numBits
--   · rw [Nat.min_eq_left h]
--     have : ↑x * 2 < ((2 : Int) ^ (I16.numBits - 1) * 2) := by grind
--     rwa [pow_sub_one_mul I16.numBits_nonzero] at this
--   · rw [Nat.min_eq_right (by grind)]
--     have := (IScalar.hBounds x).1
--     have : ↑x * 2 < ((2 : Int) ^ (numBits - 1) * 2) := by grind [numBits_eq]
--     rwa [pow_sub_one_mul numBits_nonzero] at this


end Aeneas.Std
