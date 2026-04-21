import Aeneas.Std.Scalar.Ops.Rem
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Checked Remainder: Definitions
-/

/- [core::num::{T}::checked_rem] -/
uscalar def «%S».checked_rem (x y : «%S») : Option «%S» :=
  Option.ofResult (x.rem y)

/- [core::num::{T}::checked_rem] -/
iscalar def «%S».checked_rem (x y : «%S») : Option «%S» :=
  Option.ofResult (x.rem y)

/-!
# Checked Remainder: Theorems
-/

/-!
Unsigned checked remainder
-/
uscalar @[step_pure «%S».checked_rem x y]
theorem «%S».checked_rem_bv_spec (x y : «%S») :
  match «%S».checked_rem x y with
  | some z => y.toNat ≠ 0 ∧ z.toNat = x.toNat % y.toNat ∧ z.toBitVec = x.toBitVec % y.toBitVec
  | none => y.toNat = 0 := by
  simp [checked_rem, Option.ofResult, rem]
  split_ifs
  . zify at *; simp_all
  . rename_i hnz
    simp
    have hnz' : y.toNat ≠ 0 := by zify at *; simp_all
    have : x %? y = UScalar.rem x y := by rfl
    have ⟨_, hz⟩ := spec_imp_exists (UScalar.rem_toBitVec_spec x hnz')
    simp [this, UScalar.rem, hnz] at hz
    simp [hz, hnz']

/-!
Signed checked rem
-/
iscalar @[step_pure «%S».checked_rem x y]
theorem «%S».checked_rem_bv_spec (x y : «%S») :
  match «%S».checked_rem x y with
  | some z => y.toInt ≠ 0 ∧ z.toInt = Int.tmod x.toInt y.toInt ∧ z.toBitVec = BitVec.srem x.toBitVec y.toBitVec
  | none => y.toInt = 0 := by
  simp [checked_rem, Option.ofResult, rem]
  split_ifs
  . zify at *; simp_all
  . rename_i hnz
    simp
    have hnz' : y.toInt ≠ 0 := by zify at *; simp_all
    have : x %? y = IScalar.rem x y := by rfl
    have ⟨_, hz⟩ := spec_imp_exists (@IScalar.rem_toBitVec_spec _ x y hnz')
    simp [this, IScalar.rem, hnz] at hz
    simp [*]

end Aeneas.Std
