import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open ScalarElab

/-!
# Overflowing Operations
-/

-- TODO: we should redefine this, in particular so that it doesn't live in the `Result` monad

def UScalar.overflowing_add {ty} (x y : UScalar ty) : UScalar ty × Bool :=
  (UScalar.ofBitVec ty (BitVec.ofNat ty.numBits (x.toNat + y.toNat)), 2^ty.numBits ≤ x.toNat + y.toNat)

def IScalar.overflowing_add (ty : IScalarTy) (x y : IScalar ty) : IScalar ty × Bool :=
  (IScalar.ofBitVec ty (BitVec.ofInt ty.numBits (x.toInt + y.toInt)),
     ¬ (-2^(ty.numBits -1) ≤ x.toInt + y.toInt ∧ x.toInt + y.toInt < 2^(ty.numBits-1)))

/- [core::num::{u8}::overflowing_add] -/
uscalar def core.num.«%S».overflowing_add := @UScalar.overflowing_add .«%S»

/- [core::num::{i8}::overflowing_add] -/
iscalar def core.num.«%S».overflowing_add := @IScalar.overflowing_add .«%S»

attribute [-simp] Bool.exists_bool

theorem UScalar.overflowing_add_eq {ty} (x y : UScalar ty) :
  let z := overflowing_add x y
  if x.toNat + y.toNat > UScalar.max ty then
    z.fst.toNat + UScalar.size ty = x.toNat + y.toNat ∧
    z.snd = true
  else
    z.fst.toNat = x.toNat + y.toNat ∧
    z.snd = false
  := by
  have hx := x.hBounds
  have hy := y.hBounds
  have hN : 0 < 2 ^ ty.numBits := by simp
  simp only [overflowing_add, UScalar.ofBitVec_toNat, BitVec.toNat_ofNat,
             UScalar.max, UScalar.size]
  split <;> rename_i hLt
  · refine ⟨?_, ?_⟩
    · have : (x.toNat + y.toNat) % 2^ty.numBits =
             (x.toBitVec.toNat + y.toBitVec.toNat - 2^ty.numBits) % 2^ty.numBits := by
        rw [Nat.mod_eq_sub_mod]
        · cases ty <;> grind
        · grind
      rw [this]; clear this

      have := @Nat.mod_eq_of_lt (x.toBitVec.toNat + y.toBitVec.toNat - 2^ty.numBits) (2^ty.numBits) (by omega)
      rw [this]; clear this
      scalar_tac
    · simp only [decide_eq_true_eq]; omega
  · refine ⟨?_, ?_⟩
    · apply Nat.mod_eq_of_lt; omega
    · simp only [decide_eq_false_iff_not, Nat.not_le]; omega

uscalar @[step_pure overflowing_add x y]
theorem core.num.«%S».overflowing_add_eq (x y : «%S») :
  let z := overflowing_add x y
  if x.toNat + y.toNat > UScalar.max .«%S» then z.fst.toNat + UScalar.size .«%S» = x.toNat + y.toNat ∧ z.snd = true
  else z.fst.toNat = x.toNat + y.toNat ∧ z.snd = false
  := UScalar.overflowing_add_eq x y

end Aeneas.Std
