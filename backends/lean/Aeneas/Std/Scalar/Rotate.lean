import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open ScalarElab

/-!
# Rotate
-/

/-!
## Rotate Left
-/

/- [core::num::{u8}::rotate_left] -/
uscalar @[step_pure_def]
def core.num.«%S».rotate_left (x : «%S») (shift : U32) : «%S» :=
  ⟨ x.toBitVec.rotateLeft shift.toNat ⟩

/- [core::num::{u8}::rotate_left] -/
iscalar @[step_pure_def]
def core.num.«%S».rotate_left (x : «%S») (shift : U32) : «%S» :=
  ⟨ x.toBitVec.rotateLeft shift.toNat ⟩

/-!
## Rotate Left
-/

/- [core::num::{u8}::rotate_right] -/
uscalar @[step_pure_def]
def core.num.«%S».rotate_right (x : «%S») (shift : U32) : «%S» :=
  ⟨ x.toBitVec.rotateLeft shift.toNat ⟩

/- [core::num::{u8}::rotate_right] -/
iscalar @[step_pure_def]
def core.num.«%S».rotate_right (x : «%S») (shift : U32) : «%S» :=
  ⟨ x.toBitVec.rotateLeft shift.toNat ⟩

end Aeneas.Std
