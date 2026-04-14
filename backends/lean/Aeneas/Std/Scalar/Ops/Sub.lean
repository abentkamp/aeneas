import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec
import Aeneas.Std.Scalar.Ops.CheckedArith

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Subtraction: Definitions
-/

def UScalar.sub {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  if x.toNat < y.toNat then fail .integerOverflow
  else ok (UScalar.ofBitVec ty (BitVec.ofNat _ (x.toNat - y.toNat)))

def IScalar.sub {ty : IScalarTy} (x y : IScalar ty) : Result (IScalar ty) :=
  IScalar.tryMk ty (x.toInt - y.toInt)

def UScalar.try_sub {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (sub x y)

def IScalar.try_sub {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (sub x y)

instance {ty} : HCheckedSub (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hCheckedSub x y := UScalar.sub x y

instance {ty} : HCheckedSub (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hCheckedSub x y := IScalar.sub x y

instance : HCheckedSub UInt8   UInt8   (Result UInt8)   := ⟨@UScalar.sub .U8⟩
instance : HCheckedSub UInt16  UInt16  (Result UInt16)  := ⟨@UScalar.sub .U16⟩
instance : HCheckedSub UInt32  UInt32  (Result UInt32)  := ⟨@UScalar.sub .U32⟩
instance : HCheckedSub UInt64  UInt64  (Result UInt64)  := ⟨@UScalar.sub .U64⟩
instance : HCheckedSub UInt128 UInt128 (Result UInt128) := ⟨@UScalar.sub .U128⟩
instance : HCheckedSub USize   USize   (Result USize)   := ⟨@UScalar.sub .Usize⟩
instance : HCheckedSub Int8    Int8    (Result Int8)    := ⟨@IScalar.sub .I8⟩
instance : HCheckedSub Int16   Int16   (Result Int16)   := ⟨@IScalar.sub .I16⟩
instance : HCheckedSub Int32   Int32   (Result Int32)   := ⟨@IScalar.sub .I32⟩
instance : HCheckedSub Int64   Int64   (Result Int64)   := ⟨@IScalar.sub .I64⟩
instance : HCheckedSub Int128  Int128  (Result Int128)  := ⟨@IScalar.sub .I128⟩
instance : HCheckedSub ISize   ISize   (Result ISize)   := ⟨@IScalar.sub .Isize⟩

/-!
# Subtraction: Theorems
-/

theorem UScalar.sub_equiv {ty} (x y : UScalar ty) :
  match x -? y with
  | ok z =>
    y.toNat ≤ x.toNat ∧
    x.toNat = z.toNat + y.toNat ∧
    z.toBitVec = x.toBitVec - y.toBitVec
  | fail _ => x.toNat < y.toNat
  | _ => ⊥ := by
  have : (x -? y : Result (UScalar ty)) = UScalar.sub x y := rfl
  simp [this, UScalar.sub]
  dcases h : x.toNat < y.toNat <;> simp [h]
  simp_all
  split_conjs
  . have: (x.toNat - y.toNat) % 2^ty.numBits = x.toNat - y.toNat := by
      have : 0 < 2^ty.numBits := by simp
      have := x.hBounds
      apply Nat.mod_eq_of_lt; omega
    simp [this]
    omega
  . zify; simp
    have : (x.toNat - y.toNat : Nat) = (x.toNat : Int) - y.toNat := by omega
    rw [this]; clear this
    ring_nf
    rw [Int.add_emod]
    have : ((2^ty.numBits - y.toNat) : Nat) % (2^ty.numBits : Int) =
           (- (y.toNat : Int)) % (2^ty.numBits : Int) := by
      have : (2^ty.numBits - y.toNat : Nat) = (2^ty.numBits : Int) - y.toNat := by
        have hBounds := y.hBounds
        zify at *; simp at *
        have : (2^ty.numBits : Nat) = (2^ty.numBits : Int) := by simp
        omega
      rw [this]
      -- TODO: Int.emod_sub_emod not in this version of mathlib
      have := Int.emod_add_emod (2^ty.numBits) (2^ty.numBits) (-y.toNat)
      ring_nf at this
      ring_nf
      rw [← this]
      simp
    rw [this]
    rw [← Int.add_emod]
    ring_nf

theorem IScalar.sub_equiv {ty} (x y : IScalar ty) :
  match x -? y with
  | ok z =>
    IScalar.inBounds ty (x.toInt - y.toInt) ∧
    z.toInt = x.toInt - y.toInt ∧
    z.toBitVec = x.toBitVec - y.toBitVec
  | fail _ => ¬ (IScalar.inBounds ty (x.toInt - y.toInt))
  | _ => ⊥ := by
  have : (x -? y : Result (IScalar ty)) = IScalar.sub x y := rfl
  simp [this, IScalar.sub]
  have h := tryMk_eq ty (↑x - ↑y)
  simp [inBounds] at h
  split at h <;> simp_all
  apply BitVec.eq_of_toInt_eq
  simp
  have := bmod_pow_numBits_eq_of_lt ty (x.toInt - y.toInt) (by omega) (by omega)
  simp [*]

/-!
Theorems with a specification which uses integers and bit-vectors
-/

/- Generic theorem - shouldn't be used much -/
theorem UScalar.sub_bv_spec {ty} {x y : UScalar ty}
  (h : y.toNat ≤ x.toNat) :
  x -? y ⦃ z => z.toNat = x.toNat - y.toNat ∧ y.toNat ≤ x.toNat ∧ z.toBitVec = x.toBitVec - y.toBitVec ⦄ := by
  have h := @sub_equiv ty x y
  split at h <;> simp_all
  omega

/- Generic theorem - shouldn't be used much -/
theorem IScalar.sub_bv_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x - ↑y)
  (hmax : ↑x - ↑y ≤ IScalar.max ty) :
  x -? y ⦃ z => z.toInt = ↑x - ↑y ∧ z.toBitVec = x.toBitVec - y.toBitVec ⦄ := by
  have h := @sub_equiv ty x y
  split at h <;> simp_all [min, max]
  omega

uscalar theorem «%S».sub_bv_spec {x y : «%S»} (h : y.toNat ≤ x.toNat) :
  x -? y ⦃ z => z.toNat = x.toNat - y.toNat ∧ y.toNat ≤ x.toNat ∧ z.toBitVec = x.toBitVec - y.toBitVec ⦄ :=
  UScalar.sub_bv_spec h

iscalar theorem «%S».sub_bv_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x - ↑y) (hmax : ↑x - ↑y ≤ «%S».max) :
  x -? y ⦃ z => z.toInt = ↑x - ↑y ∧ z.toBitVec = x.toBitVec - y.toBitVec ⦄ :=
  IScalar.sub_bv_spec (by scalar_tac) (by scalar_tac)

/-!
Theorems with a specification which only uses integers
-/

/- Generic theorem - shouldn't be used much -/
@[step]
theorem UScalar.sub_spec {ty} {x y : UScalar ty}
  (h : y.toNat ≤ x.toNat) :
  x -? y ⦃ z => z.toNat = x.toNat - y.toNat ∧ y.toNat ≤ x.toNat ⦄ := by
  have h := @sub_equiv ty x y
  split at h <;> simp_all
  omega

/- Generic theorem - shouldn't be used much -/
@[step]
theorem IScalar.sub_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x - ↑y)
  (hmax : ↑x - ↑y ≤ IScalar.max ty) :
  x -? y ⦃ z => z.toInt = ↑x - ↑y ⦄ := by
  have h := @sub_equiv ty x y
  split at h <;> simp_all [min, max]
  omega

uscalar @[step] theorem «%S».sub_spec {x y : «%S»} (h : y.toNat ≤ x.toNat) :
  x -? y ⦃ z => (↑z : Nat) = x.toNat - y.toNat ∧ y.toNat ≤ x.toNat ⦄ :=
  UScalar.sub_spec h

iscalar @[step] theorem «%S».sub_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x - ↑y) (hmax : ↑x - ↑y ≤ «%S».max) :
  x -? y ⦃ z => (↑z : Int) = ↑x - ↑y ⦄ :=
  IScalar.sub_spec (by scalar_tac) (by scalar_tac)

end Aeneas.Std
