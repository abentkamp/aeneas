import Aeneas.Std.Scalar.Ops.Mul
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error Arith ScalarElab

/-!
# Checked Multiplication: Definitions
-/

/- [core::num::{T}::checked_mul] -/
uscalar def «%S».checked_mul (x y : «%S») : Option «%S» :=
  Option.ofResult (x *? y)

/- [core::num::{T}::checked_mul] -/
iscalar def «%S».checked_mul (x y : «%S») : Option «%S» :=
  Option.ofResult (x *? y)

/-!
# Checked Mul: Theorems
-/

/-!
Unsigned checked mul
-/
uscalar @[step_pure «%S».checked_mul x y]
theorem «%S».checked_mul_bv_spec (x y : «%S») :
  match «%S».checked_mul x y with
  | some z => x.toNat * y.toNat ≤ «%S».max ∧ z.toNat = x.toNat * y.toNat ∧ z.toBitVec = x.toBitVec * y.toBitVec
  | none => «%S».max < x.toNat * y.toNat := by
  simp_all [checked_mul, Option.ofResult]; grind [mul_equiv]

/-!
Signed checked mul
-/
iscalar @[step_pure «%S».checked_mul x y]
theorem «%S».checked_mul_bv_spec (x y : «%S») :
  match «%S».checked_mul x y with
  | some z => «%S».min ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt ≤ «%S».max ∧ z.toInt = x.toInt * y.toInt ∧ z.toBitVec = x.toBitVec * y.toBitVec
  | none => ¬ («%S».min ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt ≤ «%S».max) := by
  have h := mul_equiv x y
  have hMul : x *? y = mul x y := by rfl
  rw [hMul] at h
  cases hEq : mul x y <;> simp_all [Option.ofResult, checked_mul, min, max]

end Aeneas.Std
