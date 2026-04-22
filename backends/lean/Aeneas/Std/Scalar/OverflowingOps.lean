import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac.Lemmas

namespace Aeneas.Std

open ScalarElab

/-!
# Overflowing Operations
-/

-- TODO: we should redefine this, in particular so that it doesn't live in the `Result` monad

/- [core::num::{u8}::overflowing_add] -/
uscalar def core.num.«%S».overflowing_add (x y : «%S») : «%S» × Bool :=
  (⟨ BitVec.ofNat _ (x.toNat + y.toNat) ⟩, 2^«%S».numBits ≤ x.toNat + y.toNat)

/- [core::num::{i8}::overflowing_add] -/
iscalar def core.num.«%S».overflowing_add (x y : «%S») : «%S» × Bool :=
  (⟨ BitVec.ofInt _ (x.toInt + y.toInt) ⟩,
     ¬ (-2^(«%S».numBits -1) ≤ x.toInt + y.toInt ∧ x.toInt + y.toInt < 2^(«%S».numBits-1)))

attribute [-simp] Bool.exists_bool

uscalar @[step_pure overflowing_add x y]
theorem core.num.«%S».overflowing_add_eq (x y : «%S») :
  let z := core.num.«%S».overflowing_add x y
  if x.toNat + y.toNat > «%S».max then
    z.fst.toNat + «%S».size = x.toNat + y.toNat ∧
    z.snd = true
  else
    z.fst.toNat = x.toNat + y.toNat ∧
    z.snd = false
  := by
  simp [core.num.«%S».overflowing_add]
  simp only [UScalar.toNat, «%S».numBits_eq, UScalarTy.numBits, BitVec.toNat_ofNat]
  split <;> rename_i hLt
  . split_conjs
    . have : (x.toBitVec.toNat + y.toBitVec.toNat) % 2^%BitWidth =
             (x.toBitVec.toNat + y.toBitVec.toNat - 2^%BitWidth) % 2^%BitWidth := by
        rw [Nat.mod_eq_sub_mod]
        scalar_tac
      rw [this]; clear this
      have := @Nat.mod_eq_of_lt (x.toBitVec.toNat + y.toBitVec.toNat - 2^%BitWidth) (2^%BitWidth) (by omega)
      rw [this]; clear this
      simp [«%S».size]
      scalar_tac
    . scalar_tac
  . split_conjs
    . apply Nat.mod_eq_of_lt
      scalar_tac
    . scalar_tac

end Aeneas.Std
