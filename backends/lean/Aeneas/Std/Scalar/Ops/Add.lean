import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Addition: Definitions
-/

uscalar def «%S».add (x y : «%S») : Result «%S» :=
  tryMk (x.toNat + y.toNat)

iscalar def «%S».add (x y : «%S») : Result «%S» :=
  tryMk (x.toInt + y.toInt)

scalar def «%S».try_add (x y : «%S») : Option «%S» :=
  Option.ofResult (add x y)

class ResultAdd (α : Type u) where
  add : α → α → Result α

infixl:65 " +? " => ResultAdd.add

scalar instance : ResultAdd «%S» where
  add x y := «%S».add x y

/-!
# Addition: Theorems
-/

uscalar theorem «%S».add_equiv (x y : «%S») :
  match x +? y with
  | ok z => x.toNat + y.toNat < «%S».size ∧
    z.toNat = x.toNat + y.toNat ∧
    z.toBitVec = x.toBitVec + y.toBitVec
  | fail _ => ¬ («%S».inBounds (x.toNat + y.toNat))
  | _ => ⊥ := by
  have : x +? y = add x y := by rfl
  rw [this]
  simp [add]
  have h := tryMk_eq (↑x + ↑y)
  simp [inBounds] at h
  split at h <;> simp_all
  zify
  zify at h
  have := @Int.emod_eq_of_lt (x.toNat + y.toNat) «%S».size (by omega) (by scalar_tac)
  simp_all [size_eq]

iscalar theorem «%S».add_equiv (x y : «%S») :
  match x +? y with
  | ok z =>
    «%S».inBounds (x.toInt + y.toInt) ∧
    z.toInt = x.toInt + y.toInt ∧
    z.toBitVec = x.toBitVec + y.toBitVec
  | fail _ => ¬ («%S».inBounds (x.toInt + y.toInt))
  | _ => ⊥ := by
  have : x +? y = «%S».add x y := by rfl
  rw [this]
  simp [add]
  have h := tryMk_eq (↑x + ↑y)
  simp [inBounds] at h
  split at h <;> simp_all
  apply BitVec.eq_of_toInt_eq
  simp
  have := bmod_pow_numBits_eq_of_lt (x.toInt + y.toInt) (by omega) (by omega)
  simp_all

/-!
Theorems about the addition, with a specification which uses
integers and bit-vectors.
-/

uscalar theorem «%S».add_bv_spec {x y : «%S»} (hmax : x.toNat + y.toNat ≤ «%S».max) :
    x +? y ⦃ z => (↑z : Nat) = ↑x + ↑y ∧ z.toBitVec = x.toBitVec + y.toBitVec ⦄ := by
  have h := @add_equiv x y
  split at h <;> simp_all [max]
  have : 0 < 2^%BitWidth := by simp
  scalar_tac

iscalar theorem «%S».add_bv_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ «%S».max) :
  x +? y ⦃ z => (↑z : Int) = ↑x + ↑y ∧ z.toBitVec = x.toBitVec + y.toBitVec ⦄ := by
  have h := @add_equiv x y
  split at h <;> simp_all [min, max]
  scalar_tac

/-!
Theorems about the addition, with a specification which uses
only integers. Those are the most common to use, so we mark them with the
`step` attribute.
-/

uscalar @[step] theorem «%S».add_spec {x y : «%S»} (hmax : x.toNat + y.toNat ≤ «%S».max) :
  x +? y ⦃ z => (↑z : Nat) = ↑x + ↑y ⦄ := by
  have h := @add_equiv x y
  split at h <;> simp_all [max]
  have : 0 < 2^%BitWidth := by simp
  scalar_tac

iscalar @[step] theorem «%S».add_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ «%S».max) :
  x +? y ⦃ z => (↑z : Int) = ↑x + ↑y ⦄ := by
  have h := @add_equiv x y
  split at h <;> simp_all [min, max]
  scalar_tac

end Aeneas.Std
