import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Sub
-/

def UScalar.wrapping_sub {ty} (x y : UScalar ty) : UScalar ty := UScalar.ofBitVec ty (UScalar.toBitVec x - UScalar.toBitVec y)

def IScalar.wrapping_sub {ty} (x y : IScalar ty) : IScalar ty := IScalar.ofBitVec ty (IScalar.toBitVec x - IScalar.toBitVec y)

uscalar @[step_pure_def]
def «%S».wrapping_sub : «%S» → «%S» → «%S» := @UScalar.wrapping_sub UScalarTy.«%S»

iscalar @[step_pure_def]
def «%S».wrapping_sub : «%S» → «%S» → «%S»  := @IScalar.wrapping_sub IScalarTy.«%S»

/- [core::num::{_}::wrapping_sub] -/
uscalar @[step_pure_def]
def core.num.«%S».wrapping_sub : «%S» → «%S» → «%S» := @UScalar.wrapping_sub UScalarTy.«%S»

/- [core::num::{_}::wrapping_sub] -/
iscalar @[step_pure_def]
def core.num.«%S».wrapping_sub : «%S» → «%S» → «%S»  := @IScalar.wrapping_sub IScalarTy.«%S»

@[simp, bvify] theorem UScalar.wrapping_sub_bv_eq {ty} (x y : UScalar ty) :
  (wrapping_sub x y).toBitVec = UScalar.toBitVec x - UScalar.toBitVec y := by
  simp only [wrapping_sub, UScalar.ofBitVec_toBitVec]

uscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_sub_bv_eq (x y : «%S») :
  («%S».wrapping_sub x y).toBitVec = x.toBitVec - y.toBitVec :=
  UScalar.wrapping_sub_bv_eq x y

uscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_sub_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).toBitVec = x.toBitVec - y.toBitVec :=
  UScalar.wrapping_sub_bv_eq x y

@[simp, bvify] theorem IScalar.wrapping_sub_bv_eq {ty} (x y : IScalar ty) :
  (wrapping_sub x y).toBitVec = IScalar.toBitVec x - IScalar.toBitVec y := by
  simp only [wrapping_sub, IScalar.ofBitVec_toBitVec]

iscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_sub_bv_eq (x y : «%S») :
  («%S».wrapping_sub x y).toBitVec = x.toBitVec - y.toBitVec :=
  IScalar.wrapping_sub_bv_eq x y

iscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_sub_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).toBitVec = x.toBitVec - y.toBitVec :=
  IScalar.wrapping_sub_bv_eq x y

@[simp] theorem UScalar.wrapping_sub_toNat_eq {ty} (x y : UScalar ty) :
  (wrapping_sub x y).toNat = (x.toNat + (UScalar.size ty - y.toNat)) % UScalar.size ty := by
  simp only [wrapping_sub, UScalar.ofBitVec_toNat, BitVec.toNat_sub, toBitVec_toNat, size]
  ring_nf

uscalar @[simp, grind =, agrind =] theorem «%S».wrapping_sub_toNat_eq (x y : «%S») :
  («%S».wrapping_sub x y).toNat = (x.toNat + (UScalar.size .«%S» - y.toNat)) % UScalar.size .«%S» :=
  UScalar.wrapping_sub_toNat_eq x y

uscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_sub_toNat_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).toNat = (x.toNat + (UScalar.size .«%S» - y.toNat)) % UScalar.size .«%S» :=
  UScalar.wrapping_sub_toNat_eq x y

@[simp] theorem IScalar.wrapping_sub_toInt_eq {ty} (x y : IScalar ty) :
  (wrapping_sub x y).toInt = Int.bmod (x.toInt - y.toInt) (2^ty.numBits) := by
  simp only [wrapping_sub, IScalar.ofBitVec_toInt, BitVec.toInt_sub, toBitVec_toInt]

iscalar @[simp, grind =, agrind =] theorem «%S».wrapping_sub_toInt_eq (x y : «%S») :
  («%S».wrapping_sub x y).toInt = Int.bmod (x.toInt - y.toInt) (2^ %BitWidth) :=
  IScalar.wrapping_sub_toInt_eq x y

iscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_sub_toInt_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).toInt = Int.bmod (x.toInt - y.toInt) (2^ %BitWidth) :=
  IScalar.wrapping_sub_toInt_eq x y

end Aeneas.Std
