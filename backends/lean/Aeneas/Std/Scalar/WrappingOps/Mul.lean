import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Mul
-/

def UScalar.wrapping_mul {ty} (x y : UScalar ty) : UScalar ty := UScalar.ofBitVec ty (UScalar.toBitVec x * UScalar.toBitVec y)

def IScalar.wrapping_mul {ty} (x y : IScalar ty) : IScalar ty := IScalar.ofBitVec ty (IScalar.toBitVec x * IScalar.toBitVec y)

uscalar @[step_pure_def]
def «%S».wrapping_mul (x y : «%S») : «%S» := @UScalar.wrapping_mul UScalarTy.«%S» x y

iscalar @[step_pure_def]
def «%S».wrapping_mul (x y : «%S») : «%S» := @IScalar.wrapping_mul IScalarTy.«%S» x y

/- [core::num::{_}::wrapping_mul] -/
uscalar @[step_pure_def]
def core.num.«%S».wrapping_mul : «%S» → «%S» → «%S» := @UScalar.wrapping_mul UScalarTy.«%S»

/- [core::num::{_}::wrapping_mul] -/
iscalar @[step_pure_def]
def core.num.«%S».wrapping_mul : «%S» → «%S» → «%S»  := @IScalar.wrapping_mul IScalarTy.«%S»

@[simp, bvify, grind =, agrind =] theorem UScalar.wrapping_mul_bv_eq {ty} (x y : UScalar ty) :
  (wrapping_mul x y).toBitVec = UScalar.toBitVec x * UScalar.toBitVec y := by
  simp only [wrapping_mul, UScalar.ofBitVec_toBitVec]

uscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_mul_bv_eq (x y : «%S») :
  («%S».wrapping_mul x y).toBitVec = x.toBitVec * y.toBitVec :=
  UScalar.wrapping_mul_bv_eq x y

uscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_mul_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).toBitVec = x.toBitVec * y.toBitVec :=
  UScalar.wrapping_mul_bv_eq x y

@[simp, bvify, grind =, agrind =] theorem IScalar.wrapping_mul_bv_eq {ty} (x y : IScalar ty) :
  (wrapping_mul x y).toBitVec = IScalar.toBitVec x * IScalar.toBitVec y := by
  simp only [wrapping_mul, IScalar.ofBitVec_toBitVec]

iscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_mul_bv_eq (x y : «%S») :
  («%S».wrapping_mul x y).toBitVec = x.toBitVec * y.toBitVec :=
  IScalar.wrapping_mul_bv_eq x y

iscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_mul_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).toBitVec = x.toBitVec * y.toBitVec :=
  IScalar.wrapping_mul_bv_eq x y

@[simp] theorem UScalar.wrapping_mul_toNat_eq {ty} (x y : UScalar ty) :
  (wrapping_mul x y).toNat = (x.toNat * y.toNat) % (UScalar.size ty) := by
  simp only [wrapping_mul, UScalar.ofBitVec_toNat, BitVec.toNat_mul, toBitVec_toNat, size]

uscalar @[simp, grind =, agrind =] theorem «%S».wrapping_mul_toNat_eq (x y : «%S») :
  («%S».wrapping_mul x y).toNat = (x.toNat * y.toNat) % (UScalar.size .«%S») :=
  UScalar.wrapping_mul_toNat_eq x y

uscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_mul_toNat_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).toNat = (x.toNat * y.toNat) % (UScalar.size .«%S») :=
  UScalar.wrapping_mul_toNat_eq x y

@[simp] theorem IScalar.wrapping_mul_toInt_eq {ty} (x y : IScalar ty) :
  (wrapping_mul x y).toInt = Int.bmod (x.toInt * y.toInt) (2^ty.numBits) := by
  simp only [wrapping_mul, IScalar.ofBitVec_toInt, BitVec.toInt_mul, toBitVec_toInt]

iscalar @[simp, grind =, agrind =] theorem «%S».wrapping_mul_toInt_eq (x y : «%S») :
  («%S».wrapping_mul x y).toInt = Int.bmod (x.toInt * y.toInt) (2^ %BitWidth) :=
  IScalar.wrapping_mul_toInt_eq x y

iscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_mul_toInt_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).toInt = Int.bmod (x.toInt * y.toInt) (2^ %BitWidth) :=
  IScalar.wrapping_mul_toInt_eq x y

end Aeneas.Std
