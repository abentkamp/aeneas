import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec
import Aeneas.Std.Scalar.Ops.CheckedArith

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Addition: Definitions
-/
def UScalar.add {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  UScalar.tryMk ty (x.toNat + y.toNat)

def IScalar.add {ty : IScalarTy} (x y : IScalar ty) : Result (IScalar ty) :=
  IScalar.tryMk ty (x.toInt + y.toInt)

def UScalar.try_add {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (add x y)

def IScalar.try_add {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (add x y)

instance {ty} : HCheckedAdd (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hCheckedAdd x y := UScalar.add x y

instance {ty} : HCheckedAdd (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hCheckedAdd x y := IScalar.add x y

instance : HCheckedAdd UInt8   UInt8   (Result UInt8)   := ⟨@UScalar.add .U8⟩
instance : HCheckedAdd UInt16  UInt16  (Result UInt16)  := ⟨@UScalar.add .U16⟩
instance : HCheckedAdd UInt32  UInt32  (Result UInt32)  := ⟨@UScalar.add .U32⟩
instance : HCheckedAdd UInt64  UInt64  (Result UInt64)  := ⟨@UScalar.add .U64⟩
instance : HCheckedAdd UInt128 UInt128 (Result UInt128) := ⟨@UScalar.add .U128⟩
instance : HCheckedAdd USize   USize   (Result USize)   := ⟨@UScalar.add .Usize⟩
instance : HCheckedAdd Int8    Int8    (Result Int8)    := ⟨@IScalar.add .I8⟩
instance : HCheckedAdd Int16   Int16   (Result Int16)   := ⟨@IScalar.add .I16⟩
instance : HCheckedAdd Int32   Int32   (Result Int32)   := ⟨@IScalar.add .I32⟩
instance : HCheckedAdd Int64   Int64   (Result Int64)   := ⟨@IScalar.add .I64⟩
instance : HCheckedAdd Int128  Int128  (Result Int128)  := ⟨@IScalar.add .I128⟩
instance : HCheckedAdd ISize   ISize   (Result ISize)   := ⟨@IScalar.add .Isize⟩

/-!
# Addition: Theorems
-/

theorem UScalar.add_equiv {ty} (x y : UScalar ty) :
  match x +? y with
  | ok z => x.toNat + y.toNat < 2^ty.numBits ∧
    z.toNat = x.toNat + y.toNat ∧
    z.toBitVec = x.toBitVec + y.toBitVec
  | fail _ => ¬ (UScalar.inBounds ty (x.toNat + y.toNat))
  | _ => ⊥ := by
  have heq : (x +? y : Result (UScalar ty)) = UScalar.add x y := rfl
  rw [heq]
  simp only [UScalar.add]
  have h := tryMk_eq ty (↑x + ↑y)
  split at h <;> simp_all [inBounds, max]
  apply BitVec.toNat_inj.mp
  simp only [UScalar.toBitVec_toNat, BitVec.toNat_add]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem IScalar.add_equiv {ty} (x y : IScalar ty) :
  match x +? y with
  | ok z =>
    IScalar.inBounds ty (x.toInt + y.toInt) ∧
    z.toInt = x.toInt + y.toInt ∧
    z.toBitVec = x.toBitVec + y.toBitVec
  | fail _ => ¬ (IScalar.inBounds ty (x.toInt + y.toInt))
  | _ => ⊥ := by
  have heq : (x +? y : Result (IScalar ty)) = IScalar.add x y := rfl
  rw [heq]
  simp [IScalar.add]
  have h := tryMk_eq ty (↑x + ↑y)
  simp [inBounds] at h
  split at h <;> simp_all
  apply BitVec.eq_of_toInt_eq
  simp
  have := bmod_pow_numBits_eq_of_lt ty (x.toInt + y.toInt) (by omega) (by omega)
  simp [*]

/-!
Theorems about the addition, with a specification which uses
integers and bit-vectors.
-/

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.add_bv_spec {ty} {x y : UScalar ty}
  (hmax : ↑x + ↑y ≤ UScalar.max ty) :
  x +? y ⦃ z => z.toNat = ↑x + ↑y ∧ z.toBitVec = x.toBitVec + y.toBitVec ⦄ := by
  have h := @add_equiv ty x y
  split at h <;> simp_all [max]
  have : 0 < 2^ty.numBits := by simp
  omega

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.add_bv_spec {ty}  {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x + ↑y)
  (hmax : ↑x + ↑y ≤ IScalar.max ty) :
  x +? y ⦃ z => z.toInt = ↑x + ↑y ∧ z.toBitVec = x.toBitVec + y.toBitVec ⦄ := by
  have h := @add_equiv ty x y
  split at h <;> simp_all [min, max]
  omega

uscalar theorem «%S».add_bv_spec {x y : «%S»} (hmax : x.toNat + y.toNat ≤ «%S».max) :
  x +? y ⦃ z => z.toNat = ↑x + ↑y ∧ z.toBitVec = x.toBitVec + y.toBitVec ⦄ :=
  UScalar.add_bv_spec (by scalar_tac)

iscalar theorem «%S».add_bv_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ «%S».max) :
  x +? y ⦃ z => z.toInt = ↑x + ↑y ∧ z.toBitVec = x.toBitVec + y.toBitVec ⦄ :=
  IScalar.add_bv_spec (by scalar_tac) (by scalar_tac)

/-!
Theorems about the addition, with a specification which uses
only integers. Those are the most common to use, so we mark them with the
`step` attribute.
-/

/-- Generic theorem - shouldn't be used much -/
@[step]
theorem UScalar.add_spec {ty} {x y : UScalar ty}
  (hmax : ↑x + ↑y ≤ UScalar.max ty) :
  x +? y ⦃ z => z.toNat = ↑x + ↑y ⦄ := by
  have h := @add_equiv ty x y
  split at h <;> simp_all [max]
  have : 0 < 2^ty.numBits := by simp
  omega

/-- Generic theorem - shouldn't be used much -/
@[step]
theorem IScalar.add_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x + ↑y)
  (hmax : ↑x + ↑y ≤ IScalar.max ty) :
  x +? y ⦃ z => z.toInt = ↑x + ↑y ⦄ := by
  have h := @add_equiv ty x y
  split at h <;> simp_all [min, max]
  omega

uscalar @[step] theorem «%S».add_spec {x y : «%S»} (hmax : x.toNat + y.toNat ≤ «%S».max) :
  x +? y ⦃ z => (↑z : Nat) = ↑x + ↑y ⦄ :=
  UScalar.add_spec (by scalar_tac)

iscalar @[step] theorem «%S».add_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ «%S».max) :
  x +? y ⦃ z => (↑z : Int) = ↑x + ↑y ⦄ :=
  IScalar.add_spec (by scalar_tac) (by scalar_tac)

end Aeneas.Std
