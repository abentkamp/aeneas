import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Subtraction: Definitions
-/

uscalar def «%S».sub (x y : «%S») : Result «%S» :=
  if x.toNat < y.toNat then fail .integerOverflow
  else ok ⟨ BitVec.ofNat _ (x.toNat - y.toNat) ⟩

iscalar def «%S».sub (x y : «%S») : Result «%S» :=
  «%S».tryMk (x.toInt - y.toInt)

scalar def «%S».try_sub (x y : «%S») : Option «%S» :=
  Option.ofResult (sub x y)

class ResultSub (α : Type u) where
  sub : α → α → Result α

infixl:65 " -? " => ResultSub.sub

scalar instance : ResultSub «%S» where
  sub x y := «%S».sub x y

/-!
# Subtraction: Theorems
-/

uscalar theorem «%S».sub_equiv (x y : «%S») :
  match x -? y with
  | ok z =>
    y.toNat ≤ x.toNat ∧
    x.toNat = z.toNat + y.toNat ∧
    z.toBitVec = x.toBitVec - y.toBitVec
  | fail _ => x.toNat < y.toNat
  | _ => ⊥ := by
  have : x -? y = sub x y := by rfl
  simp [this, sub]
  dcases h : x.toNat < y.toNat <;> simp [h]
  simp_all
  simp only [toNat]
  simp
  split_conjs
  . have: (x.toNat - y.toNat) % «%S».size = x.toNat - y.toNat := by
      have : 0 < «%S».size := by scalar_tac
      have := x.hBounds
      apply Nat.mod_eq_of_lt; scalar_tac
    rw [«%S».size_eq] at this
    simp [this]
    omega
  . change BitVec.ofNat _ _ = _
    rw [← BitVec.ofNat_sub_ofNat_of_le _ _ (by scalar_tac) (by assumption)]
    simp

iscalar theorem «%S».sub_equiv (x y : «%S») :
  match x -? y with
  | ok z =>
    «%S».inBounds (x.toInt - y.toInt) ∧
    z.toInt = x.toInt - y.toInt ∧
    z.toBitVec = x.toBitVec - y.toBitVec
  | fail _ => ¬ («%S».inBounds (x.toInt - y.toInt))
  | _ => ⊥ := by
  have : x -? y = «%S».sub x y := by rfl
  simp [this, «%S».sub]
  have h := «%S».tryMk_eq (↑x - ↑y)
  simp [«%S».inBounds, numBits_def] at h
  split at h <;> simp_all [numBits_def]
  apply BitVec.eq_of_toInt_eq
  simp
  have := «%S».bmod_pow_numBits_eq_of_lt (x.toInt - y.toInt) (by omega) (by omega)
  simp_all

/-!
Theorems with a specification which uses integers and bit-vectors
-/

uscalar theorem «%S».sub_bv_spec {x y : «%S»} (h : y.toNat ≤ x.toNat) :
    x -? y ⦃ z => z.toNat = x.toNat - y.toNat ∧ y.toNat ≤ x.toNat ∧ z.toBitVec = x.toBitVec - y.toBitVec ⦄ := by
  have h := «%S».sub_equiv x y
  split at h <;> simp_all
  omega

iscalar theorem «%S».sub_bv_spec {x y : «%S»}
    (hmin : «%S».min ≤ ↑x - ↑y) (hmax : ↑x - ↑y ≤ «%S».max) :
    x -? y ⦃ z => (↑z : Int) = ↑x - ↑y ∧ z.toBitVec = x.toBitVec - y.toBitVec ⦄ := by
  have h := «%S».sub_equiv x y
  split at h <;> simp_all [min, max]
  scalar_tac

/-!
Theorems with a specification which only uses integers
-/

uscalar @[step] theorem «%S».sub_spec {x y : «%S»} (h : y.toNat ≤ x.toNat) :
  x -? y ⦃ z => z.toNat = x.toNat - y.toNat ∧ y.toNat ≤ x.toNat ⦄ := by
  have h := «%S».sub_equiv x y
  split at h <;> simp_all
  omega

iscalar @[step] theorem «%S».sub_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x - ↑y) (hmax : ↑x - ↑y ≤ «%S».max) :
  x -? y ⦃ z => (↑z : Int) = ↑x - ↑y ⦄ := by
  have h := «%S».sub_equiv x y
  split at h <;> simp_all
  scalar_tac

end Aeneas.Std
