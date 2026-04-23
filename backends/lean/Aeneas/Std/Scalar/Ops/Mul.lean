import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec
import Mathlib.Data.Int.Init

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Multiplication: Definitions
-/

uscalar def «%S».mul (x y : «%S») : Result «%S» :=
  tryMk (x.toNat * y.toNat)

iscalar def «%S».mul (x y : «%S») : Result «%S» :=
  tryMk (x.toInt * y.toInt)

scalar def «%S».try_mul (x y : «%S») : Option «%S» :=
  Option.ofResult (mul x y)

class ResultMul (α : Type u) where
  mul : α → α → Result α

infixl:71 " *? " => ResultMul.mul

scalar instance : ResultMul «%S» where
  mul x y := «%S».mul x y

/-!
# Multiplication: Theorems
-/

/-!
Theorems with a specification which use integers and bit-vectors
-/

uscalar theorem «%S».mul_equiv (x y : «%S») :
  match x *? y with
  | ok z => x.toNat * y.toNat ≤ «%S».max ∧ (↑z : Nat) = ↑x * ↑y ∧ z.toBitVec = x.toBitVec * y.toBitVec
  | fail _ => «%S».max < x.toNat * y.toNat
  | .div => False := by
  have : x *? y = «%S».mul x y := by rfl
  rw [this]
  simp only [mul]
  have := tryMk_eq (x.toNat * y.toNat)
  split <;> simp_all only [inBounds, true_and, not_lt, gt_iff_lt]
  simp_all only [tryMk, ofOption, tryMkOpt, check_bounds, decide_true, dite_true, ok.injEq]
  rename_i hEq; simp only [← hEq, UScalar.ofNatCore, toNat]
  split_conjs
  . simp only [toBitVec_toNat, max]; scalar_tac
  . change @BitVec.ofFin _ _ = _
    zify at this; zify;
    simp only [BitVec.ofFin_eq_ofNat, BitVec.toNat_mul, Int.natCast_emod] at *
    simp only [BitVec.toNat_ofNat]
    grind
  . have : 0 < 2^%BitWidth := by simp
    simp only [max, gt_iff_lt]
    scalar_tac

iscalar theorem «%S».mul_equiv (x y : «%S») :
  match x *? y with
  | ok z => «%S».min ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt ≤ «%S».max ∧ z.toInt = x.toInt * y.toInt ∧ z.toBitVec = x.toBitVec * y.toBitVec
  | fail _ => ¬(«%S».min ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt ≤ «%S».max)
  | .div => False := by
  have : x *? y = «%S».mul x y := by rfl
  rw [this]
  simp only [mul, not_and, not_le]
  have := tryMk_eq (x.toInt * y.toInt)
  split <;> simp_all only [inBounds, min, max, true_and, not_and, not_lt] <;>
  simp_all only [tryMk, ofOption, tryMkOpt, check_bounds, and_self, decide_true, dite_true,
    ok.injEq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] <;>
  rename_i hEq <;> simp only [← hEq, IScalar.ofIntCore, toInt] <;>
  simp only [toBitVec_toInt_eq, ← BitVec.toInt_inj, BitVec.toInt_mul]
  . split_conjs
    . scalar_tac
    . scalar_tac
    . rw [toInt]
      simp only [Int.bmod, BitVec.toInt]
      simp only [Nat.cast_pow, Nat.cast_ofNat, BitVec.toNat_ofFin, Int.ofNat_toNat]
      have this : 2 * (x.toInt * y.toInt % 2 ^ %BitWidth).toNat < 2 ^ %BitWidth ↔
            x.toInt * y.toInt % 2 ^ %BitWidth < (2 ^ %BitWidth + 1) / 2 := by
        have hdiv : (2 : ℤ) ∣ 2 ^ %BitWidth := by
          have : %BitWidth = (%BitWidth - 1) + 1 := by
            have := System.Platform.numBits_eq
            omega
          rw [this, Int.pow_succ]; simp
        have : (2^%BitWidth + 1 : Int) / 2 = 2^%BitWidth / 2 := by
          rw [Int.add_ediv_of_dvd_left] <;> [simp; apply hdiv]
        rw [this]; clear this
        have heq := @Int.div_lt_div_iff_of_dvd_of_pos (↑x * ↑y % 2 ^ %BitWidth) 1 (2 ^ %BitWidth) 2
          (by simp) (by simp) (by simp) hdiv
        simp only [EuclideanDomain.div_one, mul_one] at heq
        simp only [heq]
        have : (x.toInt * y.toInt % 2 ^ %BitWidth).toNat = x.toInt * y.toInt % 2 ^ %BitWidth := by
          scalar_tac
        scalar_tac
      simp only [IScalarTy.numBits] at *
      simp only [this]
      split <;>
      simp_all only [iff_true, sup_eq_left, ge_iff_le, iff_false, not_lt, sub_left_inj] <;> omega
  . scalar_tac

/-!
Theorems with a specification which uses integers and bit-vectors.
-/

uscalar theorem «%S».mul_bv_spec {x y : «%S»} (hmax : x.toNat * y.toNat ≤ «%S».max) :
  x *? y ⦃ z => (↑z : Nat) = ↑x * ↑y ∧ z.toBitVec = x.toBitVec * y.toBitVec ⦄ := by
  have h := @mul_equiv x y
  split at h <;> simp_all [spec_ok, spec_fail]
  omega

iscalar theorem «%S».mul_bv_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ «%S».max) :
  x *? y ⦃ z => (↑z : Int) = ↑x * ↑y ∧ z.toBitVec = x.toBitVec * y.toBitVec ⦄ := by
  have h := @mul_equiv x y
  split at h <;> simp_all [spec_ok, min, max]

/-!
Theorems with a specification which only uses integers.
-/

uscalar @[step] theorem «%S».mul_spec {x y : «%S»} (hmax : x.toNat * y.toNat ≤ «%S».max) :
  x *? y ⦃ z => (↑z : Nat) = ↑x * ↑y ⦄ := by
  have h := @mul_equiv x y
  split at h <;> simp_all [spec_ok, spec_fail]
  omega

iscalar @[step] theorem «%S».mul_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ «%S».max) :
  (x *? y) ⦃ z => (↑z : Int) = ↑x * ↑y ⦄ := by
  have h := @mul_equiv x y
  split at h <;> simp_all [spec_ok, min, max]

end Aeneas.Std
