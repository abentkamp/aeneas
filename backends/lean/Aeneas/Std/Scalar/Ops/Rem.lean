import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Remainder: Definitions
-/
def UScalar.rem {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  if y.toNat != 0 then ok ⟨ BitVec.umod x.toBitVec y.toBitVec ⟩ else fail divisionByZero

def IScalar.rem {ty : IScalarTy} (x y : IScalar ty) : Result (IScalar ty) :=
  if y.toInt != 0 then ok ⟨ BitVec.srem x.toBitVec y.toBitVec ⟩
  else fail divisionByZero

uscalar def «%S».rem (x y : «%S») : Result «%S» :=
  if y.toNat != 0 then ok ⟨ BitVec.umod x.toBitVec y.toBitVec ⟩ else fail divisionByZero

iscalar def «%S».rem (x y : «%S») : Result «%S» :=
  if y.toInt != 0 then ok ⟨ BitVec.srem x.toBitVec y.toBitVec ⟩
  else fail divisionByZero

def UScalar.try_rem {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (rem x y)

def IScalar.try_rem {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (rem x y)

class ResultMod (α : Type u) where
  mod : α → α → Result α

infixl:70 " %? " => ResultMod.mod

instance {ty} : ResultMod (UScalar ty) where
  mod x y := UScalar.rem x y

instance {ty} : ResultMod (IScalar ty) where
  mod x y := IScalar.rem x y

scalar instance : ResultMod «%S» where
  mod x y := «%S».rem x y

scalar def «%S».try_rem (x y : «%S») : Option «%S» :=
  Option.ofResult (x %? y)

/-!
# Sanity Checks
-/

/-!
The scalar division/modulo on signed machine integers 't'runcates towards 0, meaning it is
implemented by the `Int.tdiv`, `Int.tmod`, etc. definitions.
-/

namespace Tests
  -- Checking that the remainder over signed integers agrees with Rust
  #assert Int.tmod 1 2 = 1
  #assert Int.tmod (-1) 2 = -1
  #assert Int.tmod 1 (-2) = 1
  #assert Int.tmod (-1) (-2) = -1
  #assert Int.tmod 7 3 = (1:Int)
  #assert Int.tmod (-7) 3 = -1
  #assert Int.tmod 7 (-3) = 1
  #assert Int.tmod (-7) (-3) = -1

  -- Checking that the signed operation over bit-vectors agrees with Rust
  private def toBitVec_srem (x y : Int) : Int :=
    (BitVec.srem (BitVec.ofInt 32 x) (BitVec.ofInt 32 y)).toInt

  #assert toBitVec_srem 1 2 = 1
  #assert toBitVec_srem (-1) 2 = -1
  #assert toBitVec_srem 1 (-2) = 1
  #assert toBitVec_srem (-1) (-2) = -1
  #assert toBitVec_srem 7 3 = (1:Int)
  #assert toBitVec_srem (-7) 3 = -1
  #assert toBitVec_srem 7 (-3) = 1
  #assert toBitVec_srem (-7) (-3) = -1
end Tests

/-!
# Remainder: Theorems
-/

/-!
Theorems with a specification which uses integers and bit-vectors
-/

theorem UScalar.rem_toBitVec_spec {ty} (x : UScalar ty) {y : UScalar ty} (hzero : y.toNat ≠ 0) :
  x %? y ⦃ z => (↑z : Nat) = ↑x % ↑y ∧ z.toBitVec = x.toBitVec % y.toBitVec ⦄ := by
  conv => arg 1; simp [ResultMod.mod]
  simp [hzero, rem]
  simp only [toNat]
  simp

theorem IScalar.rem_toBitVec_spec {ty} (x : IScalar ty) {y : IScalar ty} (hzero : y.toInt ≠ 0) :
  x %? y ⦃ z => (↑z : Int) = Int.tmod ↑x ↑y ∧ z.toBitVec = BitVec.srem x.toBitVec y.toBitVec ⦄ := by
  conv => arg 1; simp [ResultMod.mod]
  simp only [spec_ok, rem, bne_iff_ne, ne_eq, hzero, not_false_eq_true, ↓reduceIte]
  simp only [toInt]
  simp only [BitVec.toInt_srem, toBitVec_toInt_eq, and_true]

uscalar theorem «%S».rem_bv_spec (x : «%S») {y : «%S»} (hnz : y.toNat ≠ 0) :
  x %? y ⦃ z => (↑z : Nat) = ↑x % ↑y ∧ z.toBitVec = x.toBitVec % y.toBitVec ⦄ := by
  conv => arg 1; simp [ResultMod.mod]
  simp [hnz, rem]
  simp only [UScalar.toNat]
  simp

iscalar theorem «%S».rem_bv_spec (x : «%S») {y : «%S»} (hnz : y.toInt ≠ 0) :
  x %? y ⦃ z => (↑z : Int) = Int.tmod ↑x ↑y ∧ z.toBitVec = BitVec.srem x.toBitVec y.toBitVec ⦄ :=by
  conv => arg 1; simp [ResultMod.mod]
  simp only [spec_ok, rem, bne_iff_ne, ne_eq, hnz, not_false_eq_true, ↓reduceIte]
  simp only [IScalar.toInt]
  simp only [BitVec.toInt_srem, toBitVec_toInt_eq, and_true]

/-!
Theorems with a specification which only uses integers
-/

uscalar @[step] theorem «%S».rem_spec (x : «%S») {y : «%S»} (hnz : y.toNat ≠ 0) :
  x %? y ⦃ z => (↑z : Nat) = ↑x % ↑y ⦄ :=
  spec_mono («%S».rem_bv_spec x hnz) (fun _ h => h.1)

iscalar @[step] theorem «%S».rem_spec (x : «%S») {y : «%S»} (hnz : y.toInt ≠ 0) :
  x %? y ⦃ z => (↑z : Int) = Int.tmod ↑x ↑y ⦄ :=
  spec_mono («%S».rem_bv_spec x hnz) (fun _ h => h.1)

end Aeneas.Std
