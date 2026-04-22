import Aeneas.Std.Scalar.Ops.Sub
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error Arith ScalarElab

/-!
# Checked Subtraction: Definitions
-/

/- [core::num::{T}::checked_sub] -/
uscalar def «%S».checked_sub (x y : «%S») : Option «%S» :=
  Option.ofResult (x -? y)

/- [core::num::{T}::checked_sub] -/
iscalar def «%S».checked_sub (x y : «%S») : Option «%S» :=
  Option.ofResult (x -? y)

/-!
# Checked Sub: Theorems
-/

/-!
Unsigned checked sub
-/
uscalar @[step_pure «%S».checked_sub x y]
theorem «%S».checked_sub_bv_spec (x y : «%S») :
  match «%S».checked_sub x y with
  | some z => y.toNat ≤ x.toNat ∧ z.toNat = x.toNat - y.toNat ∧ z.toBitVec = x.toBitVec - y.toBitVec
  | none => x.toNat < y.toNat := by
  have h := «%S».sub_equiv x y
  have hSub : x -? y = «%S».sub x y := by rfl
  rw [hSub] at h
  cases hEq : «%S».sub x y
    <;> simp_all [Option.ofResult, checked_sub]

/-!
Signed checked sub
-/
iscalar @[step_pure «%S».checked_sub x y]
theorem «%S».checked_sub_bv_spec (x y : «%S») :
  match «%S».checked_sub x y with
  | some z => «%S».min ≤ x.toInt - y.toInt ∧ x.toInt - y.toInt ≤ «%S».max ∧ z.toInt = x.toInt - y.toInt ∧ z.toBitVec = x.toBitVec - y.toBitVec
  | none => ¬ («%S».min ≤ x.toInt - y.toInt ∧ x.toInt - y.toInt ≤ «%S».max) := by
  have h := sub_equiv x y
  have hSub : x -? y = sub x y := by rfl
  rw [hSub] at h
  cases hEq : sub x y <;> simp_all [Option.ofResult, checked_sub, min, max] <;>
  (have : 0 < 2^%BitWidth := by simp) <;>
  scalar_tac

end Aeneas.Std
