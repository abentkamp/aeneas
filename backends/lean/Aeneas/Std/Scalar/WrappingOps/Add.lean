import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Add
-/

def UScalar.wrapping_add {ty} (x y : UScalar ty) : UScalar ty := UScalar.ofBitVec ty (x.toBitVec + y.toBitVec)

def IScalar.wrapping_add {ty} (x y : IScalar ty) : IScalar ty := IScalar.ofBitVec ty (x.toBitVec + y.toBitVec)

uscalar @[step_pure_def]
def «%S».wrapping_add (x y : «%S») : «%S» := @UScalar.wrapping_add UScalarTy.«%S» x y

iscalar @[step_pure_def]
def «%S».wrapping_add (x y : «%S») : «%S» := @IScalar.wrapping_add IScalarTy.«%S» x y

/- [core::num::{_}::wrapping_add] -/
uscalar @[step_pure_def]
def core.num.«%S».wrapping_add : «%S» → «%S» → «%S» := @UScalar.wrapping_add UScalarTy.«%S»

/- [core::num::{_}::wrapping_add] -/
iscalar @[step_pure_def]
def core.num.«%S».wrapping_add : «%S» → «%S» → «%S»  := @IScalar.wrapping_add IScalarTy.«%S»

@[simp, bvify] theorem UScalar.wrapping_add_toBitVec_eq {ty} (x y : UScalar ty) :
  (wrapping_add x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp only [wrapping_add, UScalar.ofBitVec_toBitVec]

uscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_add_toBitVec_eq (x y : «%S») :
  («%S».wrapping_add x y).toBitVec = x.toBitVec + y.toBitVec :=
  UScalar.wrapping_add_toBitVec_eq x y

uscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_add_toBitVec_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).toBitVec = x.toBitVec + y.toBitVec :=
  UScalar.wrapping_add_toBitVec_eq x y

@[simp, bvify] theorem IScalar.wrapping_add_toBitVec_eq {ty} (x y : IScalar ty) :
  (wrapping_add x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp only [wrapping_add, IScalar.ofBitVec_toBitVec]

iscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_add_toBitVec_eq (x y : «%S») :
  («%S».wrapping_add x y).toBitVec = x.toBitVec + y.toBitVec :=
  IScalar.wrapping_add_toBitVec_eq x y

iscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_add_toBitVec_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).toBitVec = x.toBitVec + y.toBitVec :=
  IScalar.wrapping_add_toBitVec_eq x y

@[simp] theorem UScalar.wrapping_add_toNat_eq {ty} (x y : UScalar ty) :
  (wrapping_add x y).toNat = (x.toNat + y.toNat) % (UScalar.size ty) := by
  simp only [wrapping_add, UScalar.ofBitVec_toNat, BitVec.toNat_add, toBitVec_toNat, size]

uscalar @[simp, grind =, agrind =] theorem «%S».wrapping_add_toNat_eq (x y : «%S») :
  («%S».wrapping_add x y).toNat = (x.toNat + y.toNat) % (UScalar.size .«%S») :=
  UScalar.wrapping_add_toNat_eq x y

uscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_add_toNat_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).toNat = (x.toNat + y.toNat) % (UScalar.size .«%S») :=
  UScalar.wrapping_add_toNat_eq x y

@[simp] theorem IScalar.wrapping_add_toInt_eq {ty} (x y : IScalar ty) :
  (wrapping_add x y).toInt = Int.bmod (x.toInt + y.toInt) (2^ty.numBits) := by
  simp only [wrapping_add, IScalar.ofBitVec_toInt, BitVec.toInt_add, toBitVec_toInt]

iscalar @[simp, grind =, agrind =] theorem «%S».wrapping_add_toInt_eq (x y : «%S») :
  («%S».wrapping_add x y).toInt = Int.bmod (x.toInt + y.toInt) (2^ %BitWidth) :=
  IScalar.wrapping_add_toInt_eq x y

iscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_add_toInt_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).toInt = Int.bmod (x.toInt + y.toInt) (2^ %BitWidth) :=
  IScalar.wrapping_add_toInt_eq x y

end Aeneas.Std
