import Aeneas.Std.Scalar.Ops.Div
import Aeneas.Std.Scalar.Ops.CheckedArith
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error Arith ScalarElab

/-!
# Checked Division: Definitions
-/

/- [core::num::{T}::checked_div] -/
def core.num.checked_div_UScalar {ty} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (x /? y)

uscalar def «%S».checked_div (x y : «%S») : Option «%S» := core.num.checked_div_UScalar x y

/- [core::num::{T}::checked_div] -/
def core.num.checked_div_IScalar {ty} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (x /? y)

iscalar def «%S».checked_div (x y : «%S») : Option «%S» := core.num.checked_div_IScalar x y

/-!
# Checked Division: Theorems
-/

/-!
Unsigned checked div
-/
theorem core.num.checked_div_UScalar_bv_spec {ty} (x y : UScalar ty) :
  match core.num.checked_div_UScalar x y with
  | some z => y.toNat ≠ 0 ∧ z.toNat = x.toNat / y.toNat ∧ z.toBitVec = x.toBitVec / y.toBitVec
  | none => y.toNat = 0 := by
  simp only [checked_div_UScalar]
  by_cases hzero : y.toNat = 0
  · have hbv : y.toBitVec = 0#ty.numBits := by
      apply BitVec.toNat_inj.mp; simp [hzero]
    have hdiv : x /? y = fail divisionByZero := by
      simp [HCheckedDiv.hCheckedDiv, UScalar.div, hbv]
    simp [hdiv, Option.ofResult, hzero]
  · obtain ⟨z, hok, hval, hbv⟩ := UScalar.div_bv_spec x hzero
    simp [hok, Option.ofResult, hzero, hval, hbv]

uscalar @[step_pure «%S».checked_div x y]
theorem «%S».checked_div_bv_spec (x y : «%S») :
  match «%S».checked_div x y with
  | some z => y.toNat ≠ 0 ∧ z.toNat = x.toNat / y.toNat ∧ z.toBitVec = x.toBitVec / y.toBitVec
  | none => y.toNat = 0 := by
  have := core.num.checked_div_UScalar_bv_spec x y
  simp_all [«%S».checked_div]
  cases h: core.num.checked_div_UScalar x y <;> simp_all

/-!
Signed checked div
-/
theorem core.num.checked_div_IScalar_bv_spec {ty} (x y : IScalar ty) :
  match core.num.checked_div_IScalar x y with
  | some z => y.toInt ≠ 0 ∧ ¬ (x.toInt = IScalar.min ty ∧ y.toInt = -1) ∧ z.toInt = Int.tdiv x.toInt y.toInt ∧ z.toBitVec = BitVec.sdiv x.toBitVec y.toBitVec
  | none => y.toInt = 0 ∨ (x.toInt = IScalar.min ty ∧ y.toInt = -1) := by
  simp only [checked_div_IScalar]
  by_cases hzero : y.toInt = 0
  · have hdiv : x /? y = fail divisionByZero := by
      simp [HCheckedDiv.hCheckedDiv, IScalar.div, hzero]
    simp [hdiv, Option.ofResult, hzero]
  · by_cases hnoOvfl : ¬ (x.toInt = IScalar.min ty ∧ y.toInt = -1)
    · obtain ⟨z, hok, hval, hbv⟩ := IScalar.div_bv_spec hzero hnoOvfl
      simp [hok, Option.ofResult, hzero, hnoOvfl, hval, hbv]
    · push_neg at hnoOvfl
      have hdiv : x /? y = fail integerOverflow := by
        simp only [HCheckedDiv.hCheckedDiv, IScalar.div, bne_iff_ne, ne_eq,
                   hzero, not_false_eq_true, ↓reduceIte]
        simp [hnoOvfl.1, hnoOvfl.2]
      simp [hdiv, Option.ofResult]
      right; exact hnoOvfl

iscalar @[step_pure «%S».checked_div x y]
theorem «%S».checked_div_bv_spec (x y : «%S») :
  match core.num.checked_div_IScalar x y with
  | some z => y.toInt ≠ 0 ∧ ¬ (x.toInt = «%S».min ∧ y.toInt = -1) ∧ z.toInt = Int.tdiv x.toInt y.toInt ∧ z.toBitVec = BitVec.sdiv x.toBitVec y.toBitVec
  | none => y.toInt = 0 ∨ (x.toInt = «%S».min ∧ y.toInt = -1) := by
  have := core.num.checked_div_IScalar_bv_spec x y
  simp_all only [IScalar.min, «%S».min, «%S».numBits]
  cases h: core.num.checked_div_IScalar x y <;> simp_all only [ne_eq, not_false_eq_true, and_self]

end Aeneas.Std
