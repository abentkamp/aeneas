import Aeneas.Std.Scalar.Ops.Add
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error Arith ScalarElab

/-!
# Checked Addition: Definitions
-/

/- [core::num::{T}::checked_add] -/
uscalar def «%S».checked_add (x y : «%S») : Option «%S» :=
  Option.ofResult (x +? y)

/- [core::num::{T}::checked_add] -/
iscalar def «%S».checked_add (x y : «%S») : Option «%S» :=
  Option.ofResult (x +? y)

/-!
# Checked Add: Theorems
-/

/-!
Unsigned checked add
-/
uscalar @[step_pure «%S».checked_add x y]
theorem «%S».checked_add_bv_spec (x y : «%S») :
  match «%S».checked_add x y with
  | some z => x.toNat + y.toNat ≤ «%S».max ∧ z.toNat = x.toNat + y.toNat ∧ z.toBitVec = x.toBitVec + y.toBitVec
  | none => «%S».max < x.toNat + y.toNat := by
  have h := UScalar.add_equiv x y
  have hAdd : x +? y = UScalar.add x y := by rfl
  rw [hAdd] at h
  cases hEq : UScalar.add x y
    <;> simp_all [Option.ofResult, checked_add, max] <;>
  scalar_tac

/-!
Signed checked add
-/
iscalar @[step_pure «%S».checked_add x y]
theorem «%S».checked_add_bv_spec (x y : «%S») :
  match «%S».checked_add x y with
  | some z => «%S».min ≤ x.toInt + y.toInt ∧ x.toInt + y.toInt ≤ «%S».max ∧ z.toInt = x.toInt + y.toInt ∧ z.toBitVec = x.toBitVec + y.toBitVec
  | none => ¬ («%S».min ≤ x.toInt + y.toInt ∧ x.toInt + y.toInt ≤ «%S».max) := by
  have h := add_equiv x y
  have hAdd : x +? y = add x y := by rfl
  rw [hAdd] at h
  cases hEq : add x y <;> simp_all [Option.ofResult, checked_add, min, max] <;>
  scalar_tac

end Aeneas.Std
