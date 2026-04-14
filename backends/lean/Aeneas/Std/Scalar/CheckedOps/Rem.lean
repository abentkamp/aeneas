import Aeneas.Std.Scalar.Ops.Rem
import Aeneas.Std.Scalar.Ops.CheckedArith
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Checked Remainder: Definitions
-/

/- [core::num::{T}::checked_rem] -/
def core.num.checked_rem_UScalar {ty} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (x %? y)

uscalar def «%S».checked_rem (x y : «%S») : Option «%S» := core.num.checked_rem_UScalar x y

/- [core::num::{T}::checked_rem] -/
def core.num.checked_rem_IScalar {ty} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (x %? y)

iscalar def «%S».checked_rem (x y : «%S») : Option «%S» := core.num.checked_rem_IScalar x y

/-!
# Checked Remained
-/

/-!
Unsigned checked remainder
-/
theorem core.num.checked_rem_UScalar_bv_spec {ty} (x y : UScalar ty) :
  match core.num.checked_rem_UScalar x y with
  | some z => y.toNat ≠ 0 ∧ z.toNat = x.toNat % y.toNat ∧ z.toBitVec = x.toBitVec % y.toBitVec
  | none => y.toNat = 0 := by
  simp only [checked_rem_UScalar]
  by_cases hzero : y.toNat = 0
  · have hdiv : x %? y = fail divisionByZero := by
      simp [HCheckedRem.hCheckedRem, UScalar.rem, hzero]
    simp [hdiv, Option.ofResult, hzero]
  · obtain ⟨z, hok, hval, hbv⟩ := spec_imp_exists (UScalar.rem_bv_spec x hzero)
    simp [hok, Option.ofResult, hzero, hval, hbv]

uscalar @[step_pure «%S».checked_rem x y]
theorem «%S».checked_rem_bv_spec (x y : «%S») :
  match «%S».checked_rem x y with
  | some z => y.toNat ≠ 0 ∧ z.toNat = x.toNat % y.toNat ∧ z.toBitVec = x.toBitVec % y.toBitVec
  | none => y.toNat = 0 := by
  have := core.num.checked_rem_UScalar_bv_spec x y
  simp_all [«%S».checked_rem]
  cases h: core.num.checked_rem_UScalar x y <;> simp_all

/-!
Signed checked rem
-/
theorem core.num.checked_rem_IScalar_bv_spec {ty} (x y : IScalar ty) :
  match core.num.checked_rem_IScalar x y with
  | some z => y.toInt ≠ 0 ∧ z.toInt = Int.tmod x.toInt y.toInt ∧ z.toBitVec = BitVec.srem x.toBitVec y.toBitVec
  | none => y.toInt = 0 := by
  simp only [checked_rem_IScalar]
  by_cases hzero : y.toInt = 0
  · have hdiv : x %? y = fail divisionByZero := by
      simp [HCheckedRem.hCheckedRem, IScalar.rem, hzero]
    simp [hdiv, Option.ofResult, hzero]
  · obtain ⟨z, hok, hval, hbv⟩ := spec_imp_exists (IScalar.rem_bv_spec x hzero)
    simp [hok, Option.ofResult, hzero, hval, hbv]

iscalar @[step_pure «%S».checked_rem x y]
theorem «%S».checked_rem_bv_spec (x y : «%S») :
  match core.num.checked_rem_IScalar x y with
  | some z => y.toInt ≠ 0 ∧ z.toInt = Int.tmod x.toInt y.toInt ∧ z.toBitVec = BitVec.srem x.toBitVec y.toBitVec
  | none => y.toInt = 0 := by
  have := core.num.checked_rem_IScalar_bv_spec x y
  cases h: core.num.checked_rem_IScalar x y <;> simp_all

end Aeneas.Std
