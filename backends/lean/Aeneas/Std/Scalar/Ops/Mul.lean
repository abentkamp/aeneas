import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec
import Mathlib.Data.Int.Init
import Aeneas.Std.Scalar.Ops.CheckedArith

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Multiplication: Definitions
-/

def UScalar.mul {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  UScalar.tryMk ty (x.toNat * y.toNat)

def IScalar.mul {ty : IScalarTy} (x y : IScalar ty) : Result (IScalar ty) :=
  IScalar.tryMk ty (x.toInt * y.toInt)

def UScalar.try_mul {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (mul x y)

def IScalar.try_mul {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (mul x y)

instance {ty} : HCheckedMul (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hCheckedMul x y := UScalar.mul x y

instance {ty} : HCheckedMul (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hCheckedMul x y := IScalar.mul x y

instance : HCheckedMul UInt8   UInt8   (Result UInt8)   := ⟨@UScalar.mul .U8⟩
instance : HCheckedMul UInt16  UInt16  (Result UInt16)  := ⟨@UScalar.mul .U16⟩
instance : HCheckedMul UInt32  UInt32  (Result UInt32)  := ⟨@UScalar.mul .U32⟩
instance : HCheckedMul UInt64  UInt64  (Result UInt64)  := ⟨@UScalar.mul .U64⟩
instance : HCheckedMul UInt128 UInt128 (Result UInt128) := ⟨@UScalar.mul .U128⟩
instance : HCheckedMul USize   USize   (Result USize)   := ⟨@UScalar.mul .Usize⟩
instance : HCheckedMul Int8    Int8    (Result Int8)    := ⟨@IScalar.mul .I8⟩
instance : HCheckedMul Int16   Int16   (Result Int16)   := ⟨@IScalar.mul .I16⟩
instance : HCheckedMul Int32   Int32   (Result Int32)   := ⟨@IScalar.mul .I32⟩
instance : HCheckedMul Int64   Int64   (Result Int64)   := ⟨@IScalar.mul .I64⟩
instance : HCheckedMul Int128  Int128  (Result Int128)  := ⟨@IScalar.mul .I128⟩
instance : HCheckedMul ISize   ISize   (Result ISize)   := ⟨@IScalar.mul .Isize⟩

/-!
# Multiplication: Theorems
-/

/-!
Theorems with a specification which use integers and bit-vectors
-/

theorem UScalar.mul_equiv {ty} (x y : UScalar ty) :
  match UScalar.mul x y with
  | ok z => x.toNat * y.toNat ≤ UScalar.max ty ∧ z.toNat = ↑x * ↑y ∧ z.toBitVec = x.toBitVec * y.toBitVec
  | fail _ => UScalar.max ty < x.toNat * y.toNat
  | .div => False := by
  simp only [UScalar.mul]
  have h := tryMk_eq ty (x.toNat * y.toNat)
  split at h <;> simp_all [inBounds, UScalar.max]
  · -- ok branch: close arithmetic part, then BitVec equality
    refine ⟨by omega, ?_⟩
    apply BitVec.toNat_inj.mp
    simp only [UScalar.toBitVec_toNat, BitVec.toNat_mul]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · -- fail branch: need 0 < 2^ty.numBits for Nat subtraction
    have h2n : 0 < 2^ty.numBits := by simp
    omega

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.mul_bv_spec {ty} {x y : UScalar ty}
  (hmax : ↑x * ↑y ≤ UScalar.max ty) :
  x *? y ⦃ z => z.toNat = ↑x * ↑y ∧ z.toBitVec = x.toBitVec * y.toBitVec ⦄ := by
  have : (x *? y : Result (UScalar ty)) = UScalar.mul x y := rfl
  have := mul_equiv x y
  split at this <;> simp_all [spec_ok, and_self, spec_fail]
  omega

theorem IScalar.mul_equiv {ty} (x y : IScalar ty) :
  match IScalar.mul x y with
  | ok z => IScalar.min ty ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt ≤ IScalar.max ty ∧ z.toInt = x.toInt * y.toInt ∧ z.toBitVec = x.toBitVec * y.toBitVec
  | fail _ => ¬(IScalar.min ty ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt ≤ IScalar.max ty)
  | .div => False := by
  simp only [IScalar.mul]
  have h := tryMk_eq ty (x.toInt * y.toInt)
  simp [inBounds] at h
  split at h <;> simp_all [IScalar.min, IScalar.max]
  · -- ok branch: close arithmetic part, then BitVec equality
    refine ⟨by omega, ?_⟩
    apply BitVec.eq_of_toInt_eq
    simp
    have := bmod_pow_numBits_eq_of_lt ty (x.toInt * y.toInt) (by omega) (by omega)
    simp [*]
  · -- fail branch: -2^(n-1) ≤ ↑x * ↑y → 2^(n-1) - 1 < ↑x * ↑y
    intro hA; have := h hA; omega

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.mul_bv_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ IScalar.max ty) :
  x *? y ⦃ z => z.toInt = ↑x * ↑y ∧ z.toBitVec = x.toBitVec * y.toBitVec ⦄ := by
  have : (x *? y : Result (IScalar ty)) = IScalar.mul x y := rfl
  have := mul_equiv x y
  split at this <;> simp_all

uscalar theorem «%S».mul_bv_spec {x y : «%S»} (hmax : x.toNat * y.toNat ≤ «%S».max) :
  x *? y ⦃ z => z.toNat = ↑x * ↑y ∧ z.toBitVec = x.toBitVec * y.toBitVec ⦄ :=
  UScalar.mul_bv_spec (by scalar_tac)

iscalar theorem «%S».mul_bv_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ «%S».max) :
  x *? y ⦃ z => z.toInt = ↑x * ↑y ∧ z.toBitVec = x.toBitVec * y.toBitVec ⦄ :=
  IScalar.mul_bv_spec (by scalar_tac) (by scalar_tac)

/-!
Theorems with a specification which only use integers
-/

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.mul_spec {ty} {x y : UScalar ty}
  (hmax : ↑x * ↑y ≤ UScalar.max ty) :
  x *? y ⦃ z => z.toNat = ↑x * ↑y ⦄ := by
  apply spec_mono
  apply mul_bv_spec hmax
  grind

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.mul_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ IScalar.max ty) :
  x *? y ⦃ z => z.toInt = ↑x * ↑y ⦄ := by
  apply spec_mono
  apply @mul_bv_spec ty x y (by scalar_tac) (by scalar_tac)
  grind

uscalar @[step] theorem «%S».mul_spec {x y : «%S»} (hmax : x.toNat * y.toNat ≤ «%S».max) :
  x *? y ⦃ z => (↑z : Nat) = ↑x * ↑y ⦄ :=
  UScalar.mul_spec (by scalar_tac)

iscalar @[step] theorem «%S».mul_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ «%S».max) :
  (x *? y) ⦃ z => (↑z : Int) = ↑x * ↑y ⦄ :=
  IScalar.mul_spec (by scalar_tac) (by scalar_tac)

end Aeneas.Std
