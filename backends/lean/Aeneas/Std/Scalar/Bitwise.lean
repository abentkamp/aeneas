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
def UScalar.shiftLeft {ty : UScalarTy} (x : UScalar ty) (s : Nat) :
  Result (UScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.toBitVec.shiftLeft s ⟩
  else fail .integerOverflow

def UScalar.shiftRight {ty : UScalarTy} (x : UScalar ty) (s : Nat) :
  Result (UScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.toBitVec.ushiftRight s ⟩
  else fail .integerOverflow

def UScalar.shiftLeft_UScalar {ty tys} (x : UScalar ty) (s : UScalar tys) :
  Result (UScalar ty) :=
  x.shiftLeft s.toNat

def UScalar.shiftRight_UScalar {ty tys} (x : UScalar ty) (s : UScalar tys) :
  Result (UScalar ty) :=
  x.shiftRight s.toNat

def UScalar.shiftLeft_IScalar {ty tys} (x : UScalar ty) (s : IScalar tys) :
  Result (UScalar ty) :=
  x.shiftLeft s.toNat

def UScalar.shiftRight_IScalar {ty tys} (x : UScalar ty) (s : IScalar tys) :
  Result (UScalar ty) :=
  x.shiftRight s.toNat

def IScalar.shiftLeft {ty : IScalarTy} (x : IScalar ty) (s : Nat) :
  Result (IScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.toBitVec.shiftLeft s ⟩
  else fail .integerOverflow

def IScalar.shiftRight {ty : IScalarTy} (x : IScalar ty) (s : Nat) :
  Result (IScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.toBitVec.sshiftRight s ⟩
  else fail .integerOverflow

def IScalar.shiftLeft_UScalar {ty tys} (x : IScalar ty) (s : UScalar tys) :
  Result (IScalar ty) :=
  x.shiftLeft s.toNat

def IScalar.shiftRight_UScalar {ty tys} (x : IScalar ty) (s : UScalar tys) :
  Result (IScalar ty) :=
  x.shiftRight s.toNat

def IScalar.shiftLeft_IScalar {ty tys} (x : IScalar ty) (s : IScalar tys) :
  Result (IScalar ty) :=
  if s.toInt ≥ 0 then
    x.shiftLeft s.toNat
  else fail .integerOverflow

def IScalar.shiftRight_IScalar {ty tys} (x : IScalar ty) (s : IScalar tys) :
  Result (IScalar ty) :=
  if s.toInt ≥ 0 then
    x.shiftRight s.toNat
  else fail .integerOverflow

class ResultShiftLeft (α : Type u) (β : Type v) where
  shiftLeft : α → β → Result α

infixl:75 " <<<? " => ResultShiftLeft.shiftLeft

instance {ty0 ty1} : ResultShiftLeft (UScalar ty0) (UScalar ty1) where
  shiftLeft x y := UScalar.shiftLeft_UScalar x y

instance {ty0 ty1} : ResultShiftLeft (UScalar ty0) (IScalar ty1) where
  shiftLeft x y := UScalar.shiftLeft_IScalar x y

instance {ty0 ty1} : ResultShiftLeft (IScalar ty0) (UScalar ty1) where
  shiftLeft x y := IScalar.shiftLeft_UScalar x y

instance {ty0 ty1} : ResultShiftLeft (IScalar ty0) (IScalar ty1) where
  shiftLeft x y := IScalar.shiftLeft_IScalar x y

class ResultShiftRight (α : Type u) (β : Type v) where
  shiftRight : α → β → Result α

infixl:75 " >>>? " => ResultShiftRight.shiftRight

instance {ty0 ty1} : ResultShiftRight (UScalar ty0) (UScalar ty1) where
  shiftRight x y := UScalar.shiftRight_UScalar x y

instance {ty0 ty1} : ResultShiftRight (UScalar ty0) (IScalar ty1) where
  shiftRight x y := UScalar.shiftRight_IScalar x y

instance {ty0 ty1} : ResultShiftRight (IScalar ty0) (UScalar ty1) where
  shiftRight x y := IScalar.shiftRight_UScalar x y

instance {ty0 ty1} : ResultShiftRight (IScalar ty0) (IScalar ty1) where
  shiftRight x y := IScalar.shiftRight_IScalar x y

/-!
Bitwise and
-/
def UScalar.and {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.toBitVec &&& y.toBitVec ⟩

def IScalar.and {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.toBitVec &&& y.toBitVec ⟩

instance {ty} : HAnd (UScalar ty) (UScalar ty) (UScalar ty) where
  hAnd x y := UScalar.and x y

instance {ty} : HAnd (IScalar ty) (IScalar ty) (IScalar ty) where
  hAnd x y := IScalar.and x y

/-!
Bitwise or
-/
def UScalar.or {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.toBitVec ||| y.toBitVec ⟩

def IScalar.or {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.toBitVec ||| y.toBitVec ⟩

instance {ty} : HOr (UScalar ty) (UScalar ty) (UScalar ty) where
  hOr x y := UScalar.or x y

instance {ty} : HOr (IScalar ty) (IScalar ty) (IScalar ty) where
  hOr x y := IScalar.or x y

/-!
Xor
-/
def UScalar.xor {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.toBitVec ^^^ y.toBitVec ⟩

def IScalar.xor {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.toBitVec ^^^ y.toBitVec ⟩

instance {ty} : HXor (UScalar ty) (UScalar ty) (UScalar ty) where
  hXor x y := UScalar.xor x y

instance {ty} : HXor (IScalar ty) (IScalar ty) (IScalar ty) where
  hXor x y := IScalar.xor x y

/-!
Not
-/
def UScalar.not {ty} (x : UScalar ty) : UScalar ty := ⟨ ~~~x.toBitVec ⟩

def IScalar.not {ty} (x : IScalar ty) : IScalar ty := ⟨ ~~~x.toBitVec ⟩

instance {ty} : Complement (UScalar ty) where
  complement x := UScalar.not x

instance {ty} : Complement (IScalar ty) where
  complement x := IScalar.not x

/-!
# Bitwise Operations: Theorems
-/


/-!
## Bit shifts
-/

open Lean in
set_option hygiene false in
run_cmd do
  for ty in [`U8, `U16, `U32, `U64, `U128, `Usize] do
    Lean.Elab.Command.elabCommand (← `(
      uscalar @[step] theorem $(mkIdent s!"«%S».ShiftRight_{ty.toString}_spec".toName) (x : «%S») (y : $(mkIdent ty))
        (hy : y.toNat < %BitWidth) :
        (x >>>? y) ⦃ z =>
        z.toNat = x.toNat >>> y.toNat ∧
        z.toBitVec = x.toBitVec >>> y.toNat ⦄
        := by
        simp only [spec_ok, ResultShiftRight.shiftRight, UScalar.shiftRight_UScalar,
          UScalar.shiftRight, hy, reduceIte, «%S».size, numBits, UScalarTy.numBits]
        simp only [BitVec.ushiftRight_eq, UScalar.toNat]
        simp only [BitVec.toNat_ushiftRight, toBitVec_toNat, and_true]
    ))

open Lean in
set_option hygiene false in
run_cmd do
  for ty in [`I8, `I16, `I32, `I64, `I128, `Isize] do
    Lean.Elab.Command.elabCommand (← `(
      uscalar @[step] theorem $(mkIdent s!"«%S».ShiftRight_{ty.toString}_spec".toName) (x : «%S») (y : $(mkIdent ty))
        (_hy0 : 0 ≤ y.toNat) (hy1 : y.toNat < %BitWidth) :
        (x >>>? y) ⦃ z =>
        z.toNat = x.toNat >>> y.toNat ∧
        z.toBitVec = x.toBitVec >>> y.toNat ⦄
        := by
        simp only [spec_ok, ResultShiftRight.shiftRight, UScalar.shiftRight_IScalar,
          UScalar.shiftRight, hy1, reduceIte, «%S».size, numBits, UScalarTy.numBits]
        simp only [BitVec.ushiftRight_eq, UScalar.toNat, Nat.instShiftRight]
        simp only [IScalar.toNat, BitVec.toNat_ushiftRight, toBitVec_toNat, and_self]
    ))

open Lean in
set_option hygiene false in
run_cmd do
  for ty in [`U8, `U16, `U32, `U64, `U128, `Usize] do
    Lean.Elab.Command.elabCommand (← `(
      uscalar @[step] theorem $(mkIdent s!"«%S».ShiftLeft_{ty.toString}_spec".toName) (x : «%S») (y : $(mkIdent ty))
        (hy : y.toNat < %BitWidth) :
        (x <<<? y) ⦃ z =>
        z.toNat = (x.toNat <<< y.toNat) % «%S».size ∧
        z.toBitVec = x.toBitVec <<< y.toNat ⦄
        := by
        simp only [spec_ok, ResultShiftLeft.shiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft, hy, reduceIte,
          «%S».size, numBits, UScalarTy.numBits]
        simp only [BitVec.shiftLeft_eq, UScalar.toNat, UScalarTy.numBits]
        simp only [toBitVec_toNat, BitVec.toNat_shiftLeft, and_self]
    ))

open Lean in
set_option hygiene false in
run_cmd do
  for ty in [`I8, `I16, `I32, `I64, `I128, `Isize] do
    Lean.Elab.Command.elabCommand (← `(
      uscalar @[step] theorem $(mkIdent s!"«%S».ShiftLeft_{ty.toString}_spec".toName) (x : «%S») (y : $(mkIdent ty))
        (_hy0 : 0 ≤ y.toNat) (hy1 : y.toNat < %BitWidth) :
        (x <<<? y) ⦃ z =>
        z.toNat = (x.toNat <<< y.toNat) % «%S».size ∧
        z.toBitVec = x.toBitVec <<< y.toNat ⦄
        := by
        simp only [spec_ok, ResultShiftLeft.shiftLeft, UScalar.shiftLeft_IScalar, UScalar.shiftLeft, hy1, reduceIte,
          «%S».size, numBits, UScalarTy.numBits]
        simp only [BitVec.shiftLeft_eq, UScalar.toNat, UScalarTy.numBits]
        simp only [IScalar.toNat, BitVec.toNat_shiftLeft, toBitVec_toNat, and_self]
    ))

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
