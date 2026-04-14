import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Mul
-/

def UScalar.wrapping_mul {ty} (x y : UScalar ty) : UScalar ty := UScalar.ofBitVec ty (x.bv * y.bv)

def IScalar.wrapping_mul {ty} (x y : IScalar ty) : IScalar ty := IScalar.ofBitVec ty (x.bv * y.bv)

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
  (wrapping_mul x y).bv = x.bv * y.bv := by
  simp only [wrapping_mul, UScalar.ofBitVec_bv]

uscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_mul_bv_eq (x y : «%S») :
  («%S».wrapping_mul x y).bv = x.bv * y.bv :=
  UScalar.wrapping_mul_bv_eq x y

uscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_mul_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).bv = x.bv * y.bv :=
  UScalar.wrapping_mul_bv_eq x y

@[simp, bvify, grind =, agrind =] theorem IScalar.wrapping_mul_bv_eq {ty} (x y : IScalar ty) :
  (wrapping_mul x y).bv = x.bv * y.bv := by
  simp only [wrapping_mul, IScalar.ofBitVec_bv]

iscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_mul_bv_eq (x y : «%S») :
  («%S».wrapping_mul x y).bv = x.bv * y.bv :=
  IScalar.wrapping_mul_bv_eq x y

iscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_mul_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).bv = x.bv * y.bv :=
  IScalar.wrapping_mul_bv_eq x y

@[simp] theorem UScalar.wrapping_mul_val_eq {ty} (x y : UScalar ty) :
  (wrapping_mul x y).val = (x.val * y.val) % (UScalar.size ty) := by
  simp only [wrapping_mul, UScalar.ofBitVec_val, BitVec.toNat_mul, bv_toNat, size]

uscalar @[simp, grind =, agrind =] theorem «%S».wrapping_mul_val_eq (x y : «%S») :
  («%S».wrapping_mul x y).val = (x.val * y.val) % (UScalar.size .«%S») :=
  UScalar.wrapping_mul_val_eq x y

uscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_mul_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).val = (x.val * y.val) % (UScalar.size .«%S») :=
  UScalar.wrapping_mul_val_eq x y

@[simp] theorem IScalar.wrapping_mul_val_eq {ty} (x y : IScalar ty) :
  (wrapping_mul x y).val = Int.bmod (x.val * y.val) (2^ty.numBits) := by
  simp only [wrapping_mul, IScalar.ofBitVec_val, BitVec.toInt_mul, bv_toInt_eq]

iscalar @[simp, grind =, agrind =] theorem «%S».wrapping_mul_val_eq (x y : «%S») :
  («%S».wrapping_mul x y).val = Int.bmod (x.val * y.val) (2^ %BitWidth) :=
  IScalar.wrapping_mul_val_eq x y

iscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_mul_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).val = Int.bmod (x.val * y.val) (2^ %BitWidth) :=
  IScalar.wrapping_mul_val_eq x y

end Aeneas.Std
