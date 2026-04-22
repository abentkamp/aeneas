import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Saturating Operations
-/

/-!
Saturating add: unsigned
-/

/- [core::num::{u8}::saturating_add] -/
uscalar def core.num.«%S».saturating_add (x y : «%S») : «%S» :=
  ⟨ BitVec.ofNat _ (Min.min «%S».max (x.toNat + y.toNat)) ⟩

/-!
Saturating add: signed
-/

/- [core::num::{i8}::saturating_add] -/
iscalar def core.num.«%S».saturating_add (x y : «%S») : «%S» :=
  ⟨ BitVec.ofInt _ (Max.max «%S».min (Min.min «%S».max (x.toInt + y.toInt))) ⟩

/-!
Saturating sub: unsigned
-/

/- [core::num::{u8}::saturating_sub] -/
uscalar def core.num.«%S».saturating_sub (x y : «%S») : «%S» :=
  ⟨ BitVec.ofNat _ (Max.max 0 (x.toNat - y.toNat)) ⟩

/-!
Saturating sub: signed
-/

/- [core::num::{i8}::saturating_sub] -/
iscalar def core.num.«%S».saturating_sub (x y : «%S») : «%S» :=
  ⟨ BitVec.ofInt _ (Max.max «%S».min (Min.min «%S».max (x.toInt - y.toInt))) ⟩

end Aeneas.Std
