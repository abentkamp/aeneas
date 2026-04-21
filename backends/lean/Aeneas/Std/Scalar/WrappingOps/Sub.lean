import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Sub
-/

scalar @[step_pure_def]
def «%S».wrapping_sub (x y : «%S») : «%S»  := ⟨ x.toBitVec - y.toBitVec ⟩

/- [core::num::{_}::wrapping_sub] -/
scalar @[step_pure_def]
def core.num.«%S».wrapping_sub : «%S» → «%S» → «%S» := _root_.Aeneas.Std.«%S».wrapping_sub

uscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_sub_toBitVec_eq (x y : «%S») :
  («%S».wrapping_sub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [«%S».wrapping_sub]

uscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_sub_toBitVec_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [core.num.«%S».wrapping_sub]

iscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_sub_toBitVec_eq (x y : «%S») :
  («%S».wrapping_sub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [«%S».wrapping_sub]

iscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_sub_toBitVec_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [core.num.«%S».wrapping_sub]

uscalar @[simp, grind =, agrind =] theorem «%S».wrapping_sub_toNat_eq (x y : «%S») :
  («%S».wrapping_sub x y).toNat = (x.toNat + (UScalar.size .«%S» - y.toNat)) % UScalar.size .«%S» := by
  simp only [wrapping_sub, UScalar.toNat, UScalar.size]
  have : 0 < 2^«%S».numBits := by simp
  have : 2 ^ «%S».numBits - 1 + 1 = 2^«%S».numBits := by omega
  simp only [BitVec.toNat_sub, toBitVec_toNat]
  ring_nf

uscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_sub_toNat_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).toNat = (x.toNat + (UScalar.size .«%S» - y.toNat)) % UScalar.size .«%S» :=
  _root_.Aeneas.Std.«%S».wrapping_sub_toNat_eq x y

iscalar @[simp, grind =, agrind =] theorem «%S».wrapping_sub_toInt_eq (x y : «%S») :
  («%S».wrapping_sub x y).toInt = Int.bmod (x.toInt - y.toInt) (2^ %BitWidth) := by
  simp only [wrapping_sub, IScalar.toInt]
  simp only [BitVec.toInt_sub, toBitVec_toInt_eq]
  rfl

iscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_sub_toInt_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).toInt = Int.bmod (x.toInt - y.toInt) (2^ %BitWidth) :=
  _root_.Aeneas.Std.«%S».wrapping_sub_toInt_eq x y

end Aeneas.Std
