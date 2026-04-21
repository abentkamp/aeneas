import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Add
-/

scalar @[step_pure_def]
def «%S».wrapping_add (x y : «%S») : «%S» := ⟨ x.toBitVec + y.toBitVec ⟩

/- [core::num::{_}::wrapping_add] -/
scalar @[step_pure_def]
def core.num.«%S».wrapping_add : «%S» → «%S» → «%S» := _root_.Aeneas.Std.«%S».wrapping_add

uscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_add_toBitVec_eq (x y : «%S») :
  («%S».wrapping_add x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [«%S».wrapping_add]

uscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_add_toBitVec_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [core.num.«%S».wrapping_add]

iscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_add_toBitVec_eq (x y : «%S») :
  («%S».wrapping_add x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [«%S».wrapping_add]

iscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_add_toBitVec_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [core.num.«%S».wrapping_add]

uscalar @[simp, grind =, agrind =] theorem «%S».wrapping_add_toNat_eq (x y : «%S») :
  («%S».wrapping_add x y).toNat = (x.toNat + y.toNat) % UScalar.size .«%S» := by
  simp only [wrapping_add, UScalar.toNat, UScalar.size]
  have : 0 < 2^«%S».numBits := by simp
  have : 2 ^ «%S».numBits - 1 + 1 = 2^«%S».numBits := by omega
  simp only [BitVec.toNat_add, toBitVec_toNat]

uscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_add_toNat_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).toNat = (x.toNat + y.toNat) % UScalar.size .«%S» :=
  _root_.Aeneas.Std.«%S».wrapping_add_toNat_eq x y

iscalar @[simp, grind =, agrind =] theorem «%S».wrapping_add_toInt_eq (x y : «%S») :
  («%S».wrapping_add x y).toInt = Int.bmod (x.toInt + y.toInt) (2^ %BitWidth) := by
  simp only [wrapping_add, IScalar.toInt]
  simp only [BitVec.toInt_add, toBitVec_toInt_eq]
  rfl

iscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_add_toInt_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).toInt = Int.bmod (x.toInt + y.toInt) (2^ %BitWidth) :=
  _root_.Aeneas.Std.«%S».wrapping_add_toInt_eq x y

end Aeneas.Std
