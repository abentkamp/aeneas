import Aeneas.Std.Scalar.Ops.Div
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error Arith ScalarElab

/-!
# Checked Division: Definitions
-/

/- [core::num::{T}::checked_div] -/
uscalar def «%S».checked_div (x y : «%S») : Option «%S» :=
  Option.ofResult (x.div y)

/- [core::num::{T}::checked_div] -/
iscalar def «%S».checked_div (x y : «%S») : Option «%S» :=
  Option.ofResult (x.div y)

/-!
# Checked Division: Theorems
-/

/-!
Unsigned checked div
-/
uscalar @[step_pure «%S».checked_div x y]
theorem «%S».checked_div_bv_spec (x y : «%S») :
  match «%S».checked_div x y with
  | some z => y.toNat ≠ 0 ∧ z.toNat = x.toNat / y.toNat ∧ z.toBitVec = x.toBitVec / y.toBitVec
  | none => y.toNat = 0 := by
  simp [checked_div, Option.ofResult, div]
  split_ifs
  . zify at *; simp_all
  . rename_i hnz
    have hnz' : y.toNat ≠ 0 := by zify at *; simp_all
    exact ⟨by grind, by simp; rfl⟩

/-!
Signed checked div
-/
iscalar @[step_pure «%S».checked_div x y]
theorem «%S».checked_div_bv_spec (x y : «%S») :
  match «%S».checked_div x y with
  | some z => y.toInt ≠ 0 ∧ ¬ (x.toInt = «%S».min ∧ y.toInt = -1) ∧ z.toInt = Int.tdiv x.toInt y.toInt ∧ z.toBitVec = BitVec.sdiv x.toBitVec y.toBitVec
  | none => y.toInt = 0 ∨ (x.toInt = «%S».min ∧ y.toInt = -1) := by
  simp [checked_div, Option.ofResult, div]
  split_ifs
  . zify at *; simp_all
  . rename_i hnz hNoOverflow
    simp
    have hnz' : y.toInt ≠ 0 := by zify at *; simp_all
    have ⟨z, hz⟩ := @«%S».div_bv_spec x y hnz' (by simp; tauto)
    have : x /? y = div x y := by rfl
    simp [this, div, hnz] at hz
    split_ifs at hz
    simp at hz
    simp [hz, hnz']
    tauto
  . simp_all

end Aeneas.Std
