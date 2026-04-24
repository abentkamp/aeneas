import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Bitwise Operations: Definitions
-/

/-!
Bit shifts
-/

class ResultShiftLeft (α : Type u) (β : Type v) where
  shiftLeft : α → β → Result α

infixl:75 " <<<? " => ResultShiftLeft.shiftLeft

uuscalar instance : ResultShiftLeft «%S1» «%S2» where
  shiftLeft x y :=
    if y.toNat < %BitWidth1
    then ok ⟨ x.toBitVec.shiftLeft y.toNat ⟩
    else fail .integerOverflow

iuscalar instance : ResultShiftLeft «%S1» «%S2» where
  shiftLeft x y :=
    if y.toNat < %BitWidth1
    then ok ⟨ x.toBitVec.shiftLeft y.toNat ⟩
    else fail .integerOverflow

uiscalar instance : ResultShiftLeft «%S1» «%S2» where
  shiftLeft x y :=
    if 0 ≤ y.toInt ∧ y.toInt < %BitWidth1
    then ok ⟨ x.toBitVec.shiftLeft y.toNat ⟩
    else fail .integerOverflow

iiscalar instance : ResultShiftLeft «%S1» «%S2» where
  shiftLeft x y :=
    if 0 ≤ y.toInt ∧ y.toInt < %BitWidth1
    then ok ⟨ x.toBitVec.shiftLeft y.toNat ⟩
    else fail .integerOverflow

class ResultShiftRight (α : Type u) (β : Type v) where
  shiftRight : α → β → Result α

infixl:75 " >>>? " => ResultShiftRight.shiftRight

uuscalar instance : ResultShiftRight «%S1» «%S2» where
  shiftRight x y :=
    if y.toNat < %BitWidth1
    then ok ⟨ x.toBitVec.ushiftRight y.toNat ⟩
    else fail .integerOverflow

iuscalar instance : ResultShiftRight «%S1» «%S2» where
  shiftRight x y :=
    if y.toNat < %BitWidth1
    then ok ⟨ x.toBitVec.sshiftRight y.toNat ⟩
    else fail .integerOverflow

uiscalar instance : ResultShiftRight «%S1» «%S2» where
  shiftRight x y :=
    if 0 ≤ y.toInt ∧ y.toInt < %BitWidth1
    then ok ⟨ x.toBitVec.ushiftRight y.toNat ⟩
    else fail .integerOverflow

iiscalar instance : ResultShiftRight «%S1» «%S2» where
  shiftRight x y :=
    if 0 ≤ y.toInt ∧ y.toInt < %BitWidth1
    then ok ⟨ x.toBitVec.sshiftRight y.toNat ⟩
    else fail .integerOverflow

/-!
Bitwise logical operations
-/

scalar instance : HAnd «%S» «%S» «%S» where
  hAnd x y := ⟨ x.toBitVec &&& y.toBitVec ⟩

scalar instance : HOr «%S» «%S» «%S» where
  hOr x y := ⟨ x.toBitVec ||| y.toBitVec ⟩

scalar instance : HXor «%S» «%S» «%S» where
  hXor x y := ⟨ x.toBitVec ^^^ y.toBitVec ⟩

scalar instance : Complement «%S» where
  complement x := ⟨ ~~~x.toBitVec ⟩

/-!
# Bitwise Operations: Theorems
-/


/-!
## Bit shifts
-/

uuscalar @[step] theorem «%S1».ShiftRight_'S2_spec (x : «%S1») (y : «%S2»)
  (hy : y.toNat < %BitWidth1) :
  (x >>>? y) ⦃ z =>
  z.toNat = x.toNat >>> y.toNat ∧
  z.toBitVec = x.toBitVec >>> y.toNat ⦄
  := by
  simp only [spec_ok, ResultShiftRight.shiftRight, hy, reduceIte]
  simp only [BitVec.ushiftRight_eq, toNat]
  simp only [BitVec.toNat_ushiftRight, toBitVec_toNat, and_true]

uiscalar @[step] theorem «%S1».ShiftRight_'S2_spec (x : «%S1») (y : «%S2»)
  (hy0 : 0 ≤ y.toInt) (hy1 : y.toInt < %BitWidth1) :
  (x >>>? y) ⦃ z =>
  z.toNat = x.toNat >>> y.toNat ∧
  z.toBitVec = x.toBitVec >>> y.toNat ⦄
  := by
  simp only [ResultShiftRight.shiftRight, hy0, hy1, and_self, ↓reduceIte, I8.toNat,
    spec_ok]
  simp only [BitVec.ushiftRight_eq, toNat, Nat.instShiftRight]
  simp only [BitVec.toNat_ushiftRight, toBitVec_toNat, and_self]

uuscalar @[step] theorem «%S1».ShiftLeft_'S2_spec (x : «%S1») (y : «%S2»)
  (hy : y.toNat < %BitWidth1) :
  (x <<<? y) ⦃ z =>
  z.toNat = (x.toNat <<< y.toNat) % «%S1».size ∧
  z.toBitVec = x.toBitVec <<< y.toNat ⦄
  := by
  simp only [spec_ok, ResultShiftLeft.shiftLeft, hy, reduceIte,
    «%S1».size, numBits, UScalarTy.numBits]
  simp only [BitVec.shiftLeft_eq, toNat, UScalarTy.numBits]
  simp only [toBitVec_toNat, BitVec.toNat_shiftLeft, and_self]

uiscalar @[step] theorem «%S1».ShiftLeft_'S2_spec (x : «%S1») (y : «%S2»)
  (hy0 : 0 ≤ y.toInt) (hy1 : y.toInt < %BitWidth1) :
  (x <<<? y) ⦃ z =>
  z.toNat = (x.toNat <<< y.toNat) % «%S1».size ∧
  z.toBitVec = x.toBitVec <<< y.toNat ⦄
  := by
  simp only [ResultShiftLeft.shiftLeft, hy0, hy1, and_self, ↓reduceIte, I8.toNat,
    size, numBits, UScalarTy.numBits, Nat.reducePow, spec_ok]
  simp only [BitVec.shiftLeft_eq, toNat, UScalarTy.numBits]
  simp only [BitVec.toNat_shiftLeft, toBitVec_toNat, and_self]

/-!
## Bitwise And, Or
-/

uscalar @[step] theorem «%S».and_spec (x y : «%S») :
  lift (x &&& y) ⦃ z => z.toNat = (x &&& y).toNat ∧ z.toBitVec = x.toBitVec &&& y.toBitVec ⦄ := by
  simp [lift]; rfl

uscalar @[step] theorem «%S».or_spec (x y : «%S») :
  lift (x ||| y) ⦃ z => z.toNat = (x ||| y).toNat ∧ z.toBitVec = x.toBitVec ||| y.toBitVec ⦄ := by
  simp [lift]; rfl

uscalar @[step] theorem «%S».xor_spec (x y : «%S») :
  lift (x ^^^ y) ⦃ z => z.toNat = (x ^^^ y).toNat ∧ z.toBitVec = x.toBitVec ^^^ y.toBitVec ⦄ := by
  simp [lift]; rfl

iscalar @[step] theorem «%S».and_spec (x y : «%S») :
  lift (x &&& y) ⦃ z => z.toInt = (x &&& y).toInt ∧ z.toBitVec = x.toBitVec &&& y.toBitVec ⦄ := by
  simp [lift]; rfl

iscalar @[step] theorem «%S».or_spec (x y : «%S») :
  lift (x ||| y) ⦃ z => z.toInt = (x ||| y).toInt ∧ z.toBitVec = x.toBitVec ||| y.toBitVec ⦄ := by
  simp [lift]; rfl

iscalar @[step] theorem «%S».xor_spec (x y : «%S») :
  lift (x ^^^ y) ⦃ z => z.toInt = (x ^^^ y).toInt ∧ z.toBitVec = x.toBitVec ^^^ y.toBitVec ⦄ := by
  simp [lift]; rfl

scalar @[step] theorem «%S».not_spec (x : «%S») :
  lift (~~~x) ⦃ z => z = ~~~x ⦄ := by simp [lift]

scalar @[simp, bvify, grind =, agrind =] theorem «%S».toBitVec_and (x y : «%S») : (x &&& y).toBitVec = x.toBitVec &&& y.toBitVec := by rfl
scalar @[simp, bvify, grind =, agrind =] theorem «%S».toBitVec_or (x y : «%S») : (x ||| y).toBitVec = x.toBitVec ||| y.toBitVec := by rfl
scalar @[simp, bvify, grind =, agrind =] theorem «%S».toBitVec_xor (x y : «%S») : (x ^^^ y).toBitVec = x.toBitVec ^^^ y.toBitVec := by rfl
scalar @[simp, bvify, grind =, agrind =] theorem «%S».toBitVec_not (x : «%S») : (~~~x).toBitVec = ~~~x.toBitVec := by rfl

uscalar @[simp, scalar_tac_simps, grind =, agrind =] theorem «%S».toNat_and (x y : «%S») : (x &&& y).toNat = x.toNat &&& y.toNat := by rfl
uscalar @[simp, scalar_tac_simps, grind =, agrind =] theorem «%S».toNat_or (x y : «%S») : (x ||| y).toNat = x.toNat ||| y.toNat := by rfl
uscalar @[simp, scalar_tac_simps, grind =, agrind =] theorem «%S».toNat_xor (x y : «%S») : (x ^^^ y).toNat = x.toNat ^^^ y.toNat := by rfl

end Aeneas.Std
