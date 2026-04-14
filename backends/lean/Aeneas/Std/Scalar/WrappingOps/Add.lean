import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Add
-/

def UScalar.wrapping_add {ty} (x y : UScalar ty) : UScalar ty := UScalar.ofBitVec ty (x.bv + y.bv)

def IScalar.wrapping_add {ty} (x y : IScalar ty) : IScalar ty := IScalar.ofBitVec ty (x.bv + y.bv)

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

@[simp, bvify] theorem UScalar.wrapping_add_bv_eq {ty} (x y : UScalar ty) :
  (wrapping_add x y).bv = x.bv + y.bv := by
  simp only [wrapping_add, UScalar.ofBitVec_bv]

uscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_add_bv_eq (x y : «%S») :
  («%S».wrapping_add x y).bv = x.bv + y.bv :=
  UScalar.wrapping_add_bv_eq x y

uscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_add_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).bv = x.bv + y.bv :=
  UScalar.wrapping_add_bv_eq x y

@[simp, bvify] theorem IScalar.wrapping_add_bv_eq {ty} (x y : IScalar ty) :
  (wrapping_add x y).bv = x.bv + y.bv := by
  simp only [wrapping_add, IScalar.ofBitVec_bv]

iscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_add_bv_eq (x y : «%S») :
  («%S».wrapping_add x y).bv = x.bv + y.bv :=
  IScalar.wrapping_add_bv_eq x y

iscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_add_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).bv = x.bv + y.bv :=
  IScalar.wrapping_add_bv_eq x y

@[simp] theorem UScalar.wrapping_add_val_eq {ty} (x y : UScalar ty) :
  (wrapping_add x y).val = (x.val + y.val) % (UScalar.size ty) := by
  simp only [wrapping_add, UScalar.ofBitVec_val, BitVec.toNat_add, bv_toNat, size]

uscalar @[simp, grind =, agrind =] theorem «%S».wrapping_add_val_eq (x y : «%S») :
  («%S».wrapping_add x y).val = (x.val + y.val) % (UScalar.size .«%S») :=
  UScalar.wrapping_add_val_eq x y

uscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_add_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).val = (x.val + y.val) % (UScalar.size .«%S») :=
  UScalar.wrapping_add_val_eq x y

@[simp] theorem IScalar.wrapping_add_val_eq {ty} (x y : IScalar ty) :
  (wrapping_add x y).val = Int.bmod (x.val + y.val) (2^ty.numBits) := by
  simp only [wrapping_add, IScalar.ofBitVec_val, BitVec.toInt_add, bv_toInt_eq]

iscalar @[simp, grind =, agrind =] theorem «%S».wrapping_add_val_eq (x y : «%S») :
  («%S».wrapping_add x y).val = Int.bmod (x.val + y.val) (2^ %BitWidth) :=
  IScalar.wrapping_add_val_eq x y

iscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_add_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).val = Int.bmod (x.val + y.val) (2^ %BitWidth) :=
  IScalar.wrapping_add_val_eq x y

end Aeneas.Std
