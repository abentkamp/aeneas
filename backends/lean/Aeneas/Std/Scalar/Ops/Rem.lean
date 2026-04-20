import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec
import Aeneas.Std.Scalar.Ops.CheckedArith

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Remainder: Definitions
-/
def UScalar.rem {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  if y.toNat != 0 then ok (UScalar.ofBitVec ty (BitVec.umod (UScalar.toBitVec x) (UScalar.toBitVec y))) else fail divisionByZero

def IScalar.rem {ty : IScalarTy} (x y : IScalar ty) : Result (IScalar ty) :=
  if y.toInt != 0 then ok (IScalar.ofBitVec ty (BitVec.srem (IScalar.toBitVec x) (IScalar.toBitVec y)))
  else fail divisionByZero

def UScalar.try_rem {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (rem x y)

def IScalar.try_rem {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (rem x y)

instance {ty} : HCheckedRem (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hCheckedRem x y := UScalar.rem x y

instance {ty} : HCheckedRem (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hCheckedRem x y := IScalar.rem x y

instance : HCheckedRem UInt8   UInt8   (Result UInt8)   := ⟨@UScalar.rem .U8⟩
instance : HCheckedRem UInt16  UInt16  (Result UInt16)  := ⟨@UScalar.rem .U16⟩
instance : HCheckedRem UInt32  UInt32  (Result UInt32)  := ⟨@UScalar.rem .U32⟩
instance : HCheckedRem UInt64  UInt64  (Result UInt64)  := ⟨@UScalar.rem .U64⟩
instance : HCheckedRem UInt128 UInt128 (Result UInt128) := ⟨@UScalar.rem .U128⟩
instance : HCheckedRem USize   USize   (Result USize)   := ⟨@UScalar.rem .Usize⟩
instance : HCheckedRem Int8    Int8    (Result Int8)    := ⟨@IScalar.rem .I8⟩
instance : HCheckedRem Int16   Int16   (Result Int16)   := ⟨@IScalar.rem .I16⟩
instance : HCheckedRem Int32   Int32   (Result Int32)   := ⟨@IScalar.rem .I32⟩
instance : HCheckedRem Int64   Int64   (Result Int64)   := ⟨@IScalar.rem .I64⟩
instance : HCheckedRem Int128  Int128  (Result Int128)  := ⟨@IScalar.rem .I128⟩
instance : HCheckedRem ISize   ISize   (Result ISize)   := ⟨@IScalar.rem .Isize⟩

/-!
# Sanity Checks
-/

/-!
The scalar division/modulo on signed machine integers 't'runcates towards 0, meaning it is
implemented by the `Int.tdiv`, `Int.tmod`, etc. definitions.
-/

namespace Tests
  -- Checking that the remainder over signed integers agrees with Rust
  #assert Int.tmod 1 2 = 1
  #assert Int.tmod (-1) 2 = -1
  #assert Int.tmod 1 (-2) = 1
  #assert Int.tmod (-1) (-2) = -1
  #assert Int.tmod 7 3 = (1:Int)
  #assert Int.tmod (-7) 3 = -1
  #assert Int.tmod 7 (-3) = 1
  #assert Int.tmod (-7) (-3) = -1

  -- Checking that the signed operation over bit-vectors agrees with Rust
  private def bv_srem (x y : Int) : Int :=
    (BitVec.srem (BitVec.ofInt 32 x) (BitVec.ofInt 32 y)).toInt

  #assert bv_srem 1 2 = 1
  #assert bv_srem (-1) 2 = -1
  #assert bv_srem 1 (-2) = 1
  #assert bv_srem (-1) (-2) = -1
  #assert bv_srem 7 3 = (1:Int)
  #assert bv_srem (-7) 3 = -1
  #assert bv_srem 7 (-3) = 1
  #assert bv_srem (-7) (-3) = -1
end Tests

/-!
# Remainder: Theorems
-/

/-!
Theorems with a specification which uses integers and bit-vectors
-/

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.rem_bv_spec {ty} (x : UScalar ty) {y : UScalar ty} (hzero : y.toNat ≠ 0) :
  x %? y ⦃ z => z.toNat = ↑x % ↑y ∧ z.toBitVec = x.toBitVec % y.toBitVec ⦄ := by
  conv => arg 1; simp [HCheckedRem.hCheckedRem]
  simp [hzero, UScalar.rem]

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.rem_bv_spec {ty} (x : IScalar ty) {y : IScalar ty} (hzero : y.toInt ≠ 0) :
  x %? y ⦃ z => z.toInt = Int.tmod ↑x ↑y ∧ z.toBitVec = BitVec.srem x.toBitVec y.toBitVec ⦄ := by
  conv => arg 1; simp [HCheckedRem.hCheckedRem]
  simp only [spec_ok, IScalar.rem, bne_iff_ne, ne_eq, hzero, not_false_eq_true, ↓reduceIte]
  simp only [BitVec.toInt_srem, IScalar.toBitVec_toInt, IScalar.ofBitVec_toInt,
             IScalar.ofBitVec_toBitVec, and_true]


uscalar theorem «%S».rem_bv_spec (x : «%S») {y : «%S»} (hnz : y.toNat ≠ 0) :
  x %? y ⦃ z => z.toNat = ↑x % ↑y ∧ z.toBitVec = x.toBitVec % y.toBitVec ⦄ :=
  UScalar.rem_bv_spec x hnz

iscalar theorem «%S».rem_bv_spec (x : «%S») {y : «%S»} (hnz : y.toInt ≠ 0) :
  x %? y ⦃ z => z.toInt = Int.tmod ↑x ↑y ∧ z.toBitVec = BitVec.srem x.toBitVec y.toBitVec ⦄ :=
  IScalar.rem_bv_spec x hnz

/-!
Theorems with a specification which only uses integers
-/

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.rem_spec {ty} (x : UScalar ty) {y : UScalar ty} (hzero : y.toNat ≠ 0) :
  x %? y ⦃ z => z.toNat = ↑x % ↑y ⦄ := by
  apply spec_mono
  · apply rem_bv_spec x hzero
  · intros x' h
    exact h.1

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.rem_spec {ty} (x : IScalar ty) {y : IScalar ty} (hzero : y.toInt ≠ 0) :
  x %? y ⦃ z => z.toInt = Int.tmod ↑x ↑y ⦄ := by
  apply spec_mono
  · apply rem_bv_spec x hzero
  · intros x' h
    exact h.1

uscalar @[step] theorem «%S».rem_spec (x : «%S») {y : «%S»} (hnz : y.toNat ≠ 0) :
  x %? y ⦃ z => (↑z : Nat) = ↑x % ↑y ⦄ :=
  UScalar.rem_spec x hnz

iscalar @[step] theorem «%S».rem_spec (x : «%S») {y : «%S»} (hnz : y.toInt ≠ 0) :
  x %? y ⦃ z => (↑z : Int) = Int.tmod ↑x ↑y ⦄ :=
  IScalar.rem_spec x hnz

end Aeneas.Std
