import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Bitwise Operations: Definitions
-/

/-!
Bit shifts
-/
def UScalar.shiftLeft {ty : UScalarTy} (x : UScalar ty) (s : Nat) :
  Result (UScalar ty) :=
  if s < ty.numBits then
    ok (UScalar.ofBitVec ty ((UScalar.toBitVec x).shiftLeft s))
  else fail .integerOverflow

def UScalar.shiftRight {ty : UScalarTy} (x : UScalar ty) (s : Nat) :
  Result (UScalar ty) :=
  if s < ty.numBits then
    ok (UScalar.ofBitVec ty ((UScalar.toBitVec x).ushiftRight s))
  else fail .integerOverflow

def UScalar.shiftLeft_UScalar {ty tys} (x : UScalar ty) (s : UScalar tys) :
  Result (UScalar ty) :=
  x.shiftLeft s.toNat

def UScalar.shiftRight_UScalar {ty tys} (x : UScalar ty) (s : UScalar tys) :
  Result (UScalar ty) :=
  x.shiftRight s.toNat

def UScalar.shiftLeft_IScalar {ty tys} (x : UScalar ty) (s : IScalar tys) :
  Result (UScalar ty) :=
  x.shiftLeft s.toNat

def UScalar.shiftRight_IScalar {ty tys} (x : UScalar ty) (s : IScalar tys) :
  Result (UScalar ty) :=
  x.shiftRight s.toNat

def IScalar.shiftLeft {ty : IScalarTy} (x : IScalar ty) (s : Nat) :
  Result (IScalar ty) :=
  if s < ty.numBits then
    ok (IScalar.ofBitVec ty ((IScalar.toBitVec x).shiftLeft s))
  else fail .integerOverflow

def IScalar.shiftRight {ty : IScalarTy} (x : IScalar ty) (s : Nat) :
  Result (IScalar ty) :=
  if s < ty.numBits then
    ok (IScalar.ofBitVec ty ((IScalar.toBitVec x).sshiftRight s))
  else fail .integerOverflow

def IScalar.shiftLeft_UScalar {ty tys} (x : IScalar ty) (s : UScalar tys) :
  Result (IScalar ty) :=
  x.shiftLeft s.toNat

def IScalar.shiftRight_UScalar {ty tys} (x : IScalar ty) (s : UScalar tys) :
  Result (IScalar ty) :=
  x.shiftRight s.toNat

def IScalar.shiftLeft_IScalar {ty tys} (x : IScalar ty) (s : IScalar tys) :
  Result (IScalar ty) :=
  if s.toInt ≥ 0 then
    x.shiftLeft s.toNat
  else fail .integerOverflow

def IScalar.shiftRight_IScalar {ty tys} (x : IScalar ty) (s : IScalar tys) :
  Result (IScalar ty) :=
  if s.toInt ≥ 0 then
    x.shiftRight s.toNat
  else fail .integerOverflow

instance {ty0 ty1} : HShiftLeft (UScalar ty0) (UScalar ty1) (Result (UScalar ty0)) where
  hShiftLeft x y := UScalar.shiftLeft_UScalar x y

instance {ty0 ty1} : HShiftLeft (UScalar ty0) (IScalar ty1) (Result (UScalar ty0)) where
  hShiftLeft x y := UScalar.shiftLeft_IScalar x y

instance {ty0 ty1} : HShiftLeft (IScalar ty0) (UScalar ty1) (Result (IScalar ty0)) where
  hShiftLeft x y := IScalar.shiftLeft_UScalar x y

instance {ty0 ty1} : HShiftLeft (IScalar ty0) (IScalar ty1) (Result (IScalar ty0)) where
  hShiftLeft x y := IScalar.shiftLeft_IScalar x y

instance {ty0 ty1} : HShiftRight (UScalar ty0) (UScalar ty1) (Result (UScalar ty0)) where
  hShiftRight x y := UScalar.shiftRight_UScalar x y

instance {ty0 ty1} : HShiftRight (UScalar ty0) (IScalar ty1) (Result (UScalar ty0)) where
  hShiftRight x y := UScalar.shiftRight_IScalar x y

instance {ty0 ty1} : HShiftRight (IScalar ty0) (UScalar ty1) (Result (IScalar ty0)) where
  hShiftRight x y := IScalar.shiftRight_UScalar x y

instance {ty0 ty1} : HShiftRight (IScalar ty0) (IScalar ty1) (Result (IScalar ty0)) where
  hShiftRight x y := IScalar.shiftRight_IScalar x y

-- Concrete HShiftRight instances: needed because the abstract instances above have head `UScalar`/`IScalar`,
-- which doesn't match when Lean reduces abbrevs to their concrete native types (e.g., U32 → UInt32).
-- Explicit type arguments are required because Lean cannot infer `IScalarTy` from `Int32` alone.

-- U × U
instance : HShiftRight UInt8   UInt8   (Result UInt8)   := ⟨@UScalar.shiftRight_UScalar .U8    .U8   ⟩
instance : HShiftRight UInt8   UInt16  (Result UInt8)   := ⟨@UScalar.shiftRight_UScalar .U8    .U16  ⟩
instance : HShiftRight UInt8   UInt32  (Result UInt8)   := ⟨@UScalar.shiftRight_UScalar .U8    .U32  ⟩
instance : HShiftRight UInt8   UInt64  (Result UInt8)   := ⟨@UScalar.shiftRight_UScalar .U8    .U64  ⟩
instance : HShiftRight UInt8   UInt128 (Result UInt8)   := ⟨@UScalar.shiftRight_UScalar .U8    .U128 ⟩
instance : HShiftRight UInt8   USize   (Result UInt8)   := ⟨@UScalar.shiftRight_UScalar .U8    .Usize⟩
instance : HShiftRight UInt16  UInt8   (Result UInt16)  := ⟨@UScalar.shiftRight_UScalar .U16   .U8   ⟩
instance : HShiftRight UInt16  UInt16  (Result UInt16)  := ⟨@UScalar.shiftRight_UScalar .U16   .U16  ⟩
instance : HShiftRight UInt16  UInt32  (Result UInt16)  := ⟨@UScalar.shiftRight_UScalar .U16   .U32  ⟩
instance : HShiftRight UInt16  UInt64  (Result UInt16)  := ⟨@UScalar.shiftRight_UScalar .U16   .U64  ⟩
instance : HShiftRight UInt16  UInt128 (Result UInt16)  := ⟨@UScalar.shiftRight_UScalar .U16   .U128 ⟩
instance : HShiftRight UInt16  USize   (Result UInt16)  := ⟨@UScalar.shiftRight_UScalar .U16   .Usize⟩
instance : HShiftRight UInt32  UInt8   (Result UInt32)  := ⟨@UScalar.shiftRight_UScalar .U32   .U8   ⟩
instance : HShiftRight UInt32  UInt16  (Result UInt32)  := ⟨@UScalar.shiftRight_UScalar .U32   .U16  ⟩
instance : HShiftRight UInt32  UInt32  (Result UInt32)  := ⟨@UScalar.shiftRight_UScalar .U32   .U32  ⟩
instance : HShiftRight UInt32  UInt64  (Result UInt32)  := ⟨@UScalar.shiftRight_UScalar .U32   .U64  ⟩
instance : HShiftRight UInt32  UInt128 (Result UInt32)  := ⟨@UScalar.shiftRight_UScalar .U32   .U128 ⟩
instance : HShiftRight UInt32  USize   (Result UInt32)  := ⟨@UScalar.shiftRight_UScalar .U32   .Usize⟩
instance : HShiftRight UInt64  UInt8   (Result UInt64)  := ⟨@UScalar.shiftRight_UScalar .U64   .U8   ⟩
instance : HShiftRight UInt64  UInt16  (Result UInt64)  := ⟨@UScalar.shiftRight_UScalar .U64   .U16  ⟩
instance : HShiftRight UInt64  UInt32  (Result UInt64)  := ⟨@UScalar.shiftRight_UScalar .U64   .U32  ⟩
instance : HShiftRight UInt64  UInt64  (Result UInt64)  := ⟨@UScalar.shiftRight_UScalar .U64   .U64  ⟩
instance : HShiftRight UInt64  UInt128 (Result UInt64)  := ⟨@UScalar.shiftRight_UScalar .U64   .U128 ⟩
instance : HShiftRight UInt64  USize   (Result UInt64)  := ⟨@UScalar.shiftRight_UScalar .U64   .Usize⟩
instance : HShiftRight UInt128 UInt8   (Result UInt128) := ⟨@UScalar.shiftRight_UScalar .U128  .U8   ⟩
instance : HShiftRight UInt128 UInt16  (Result UInt128) := ⟨@UScalar.shiftRight_UScalar .U128  .U16  ⟩
instance : HShiftRight UInt128 UInt32  (Result UInt128) := ⟨@UScalar.shiftRight_UScalar .U128  .U32  ⟩
instance : HShiftRight UInt128 UInt64  (Result UInt128) := ⟨@UScalar.shiftRight_UScalar .U128  .U64  ⟩
instance : HShiftRight UInt128 UInt128 (Result UInt128) := ⟨@UScalar.shiftRight_UScalar .U128  .U128 ⟩
instance : HShiftRight UInt128 USize   (Result UInt128) := ⟨@UScalar.shiftRight_UScalar .U128  .Usize⟩
instance : HShiftRight USize   UInt8   (Result USize)   := ⟨@UScalar.shiftRight_UScalar .Usize .U8   ⟩
instance : HShiftRight USize   UInt16  (Result USize)   := ⟨@UScalar.shiftRight_UScalar .Usize .U16  ⟩
instance : HShiftRight USize   UInt32  (Result USize)   := ⟨@UScalar.shiftRight_UScalar .Usize .U32  ⟩
instance : HShiftRight USize   UInt64  (Result USize)   := ⟨@UScalar.shiftRight_UScalar .Usize .U64  ⟩
instance : HShiftRight USize   UInt128 (Result USize)   := ⟨@UScalar.shiftRight_UScalar .Usize .U128 ⟩
instance : HShiftRight USize   USize   (Result USize)   := ⟨@UScalar.shiftRight_UScalar .Usize .Usize⟩

-- U × I
instance : HShiftRight UInt8   Int8    (Result UInt8)   := ⟨@UScalar.shiftRight_IScalar .U8    .I8   ⟩
instance : HShiftRight UInt8   Int16   (Result UInt8)   := ⟨@UScalar.shiftRight_IScalar .U8    .I16  ⟩
instance : HShiftRight UInt8   Int32   (Result UInt8)   := ⟨@UScalar.shiftRight_IScalar .U8    .I32  ⟩
instance : HShiftRight UInt8   Int64   (Result UInt8)   := ⟨@UScalar.shiftRight_IScalar .U8    .I64  ⟩
instance : HShiftRight UInt8   Int128  (Result UInt8)   := ⟨@UScalar.shiftRight_IScalar .U8    .I128 ⟩
instance : HShiftRight UInt8   ISize   (Result UInt8)   := ⟨@UScalar.shiftRight_IScalar .U8    .Isize⟩
instance : HShiftRight UInt16  Int8    (Result UInt16)  := ⟨@UScalar.shiftRight_IScalar .U16   .I8   ⟩
instance : HShiftRight UInt16  Int16   (Result UInt16)  := ⟨@UScalar.shiftRight_IScalar .U16   .I16  ⟩
instance : HShiftRight UInt16  Int32   (Result UInt16)  := ⟨@UScalar.shiftRight_IScalar .U16   .I32  ⟩
instance : HShiftRight UInt16  Int64   (Result UInt16)  := ⟨@UScalar.shiftRight_IScalar .U16   .I64  ⟩
instance : HShiftRight UInt16  Int128  (Result UInt16)  := ⟨@UScalar.shiftRight_IScalar .U16   .I128 ⟩
instance : HShiftRight UInt16  ISize   (Result UInt16)  := ⟨@UScalar.shiftRight_IScalar .U16   .Isize⟩
instance : HShiftRight UInt32  Int8    (Result UInt32)  := ⟨@UScalar.shiftRight_IScalar .U32   .I8   ⟩
instance : HShiftRight UInt32  Int16   (Result UInt32)  := ⟨@UScalar.shiftRight_IScalar .U32   .I16  ⟩
instance : HShiftRight UInt32  Int32   (Result UInt32)  := ⟨@UScalar.shiftRight_IScalar .U32   .I32  ⟩
instance : HShiftRight UInt32  Int64   (Result UInt32)  := ⟨@UScalar.shiftRight_IScalar .U32   .I64  ⟩
instance : HShiftRight UInt32  Int128  (Result UInt32)  := ⟨@UScalar.shiftRight_IScalar .U32   .I128 ⟩
instance : HShiftRight UInt32  ISize   (Result UInt32)  := ⟨@UScalar.shiftRight_IScalar .U32   .Isize⟩
instance : HShiftRight UInt64  Int8    (Result UInt64)  := ⟨@UScalar.shiftRight_IScalar .U64   .I8   ⟩
instance : HShiftRight UInt64  Int16   (Result UInt64)  := ⟨@UScalar.shiftRight_IScalar .U64   .I16  ⟩
instance : HShiftRight UInt64  Int32   (Result UInt64)  := ⟨@UScalar.shiftRight_IScalar .U64   .I32  ⟩
instance : HShiftRight UInt64  Int64   (Result UInt64)  := ⟨@UScalar.shiftRight_IScalar .U64   .I64  ⟩
instance : HShiftRight UInt64  Int128  (Result UInt64)  := ⟨@UScalar.shiftRight_IScalar .U64   .I128 ⟩
instance : HShiftRight UInt64  ISize   (Result UInt64)  := ⟨@UScalar.shiftRight_IScalar .U64   .Isize⟩
instance : HShiftRight UInt128 Int8    (Result UInt128) := ⟨@UScalar.shiftRight_IScalar .U128  .I8   ⟩
instance : HShiftRight UInt128 Int16   (Result UInt128) := ⟨@UScalar.shiftRight_IScalar .U128  .I16  ⟩
instance : HShiftRight UInt128 Int32   (Result UInt128) := ⟨@UScalar.shiftRight_IScalar .U128  .I32  ⟩
instance : HShiftRight UInt128 Int64   (Result UInt128) := ⟨@UScalar.shiftRight_IScalar .U128  .I64  ⟩
instance : HShiftRight UInt128 Int128  (Result UInt128) := ⟨@UScalar.shiftRight_IScalar .U128  .I128 ⟩
instance : HShiftRight UInt128 ISize   (Result UInt128) := ⟨@UScalar.shiftRight_IScalar .U128  .Isize⟩
instance : HShiftRight USize   Int8    (Result USize)   := ⟨@UScalar.shiftRight_IScalar .Usize .I8   ⟩
instance : HShiftRight USize   Int16   (Result USize)   := ⟨@UScalar.shiftRight_IScalar .Usize .I16  ⟩
instance : HShiftRight USize   Int32   (Result USize)   := ⟨@UScalar.shiftRight_IScalar .Usize .I32  ⟩
instance : HShiftRight USize   Int64   (Result USize)   := ⟨@UScalar.shiftRight_IScalar .Usize .I64  ⟩
instance : HShiftRight USize   Int128  (Result USize)   := ⟨@UScalar.shiftRight_IScalar .Usize .I128 ⟩
instance : HShiftRight USize   ISize   (Result USize)   := ⟨@UScalar.shiftRight_IScalar .Usize .Isize⟩

-- I × U
instance : HShiftRight Int8    UInt8   (Result Int8)    := ⟨@IScalar.shiftRight_UScalar .I8    .U8   ⟩
instance : HShiftRight Int8    UInt16  (Result Int8)    := ⟨@IScalar.shiftRight_UScalar .I8    .U16  ⟩
instance : HShiftRight Int8    UInt32  (Result Int8)    := ⟨@IScalar.shiftRight_UScalar .I8    .U32  ⟩
instance : HShiftRight Int8    UInt64  (Result Int8)    := ⟨@IScalar.shiftRight_UScalar .I8    .U64  ⟩
instance : HShiftRight Int8    UInt128 (Result Int8)    := ⟨@IScalar.shiftRight_UScalar .I8    .U128 ⟩
instance : HShiftRight Int8    USize   (Result Int8)    := ⟨@IScalar.shiftRight_UScalar .I8    .Usize⟩
instance : HShiftRight Int16   UInt8   (Result Int16)   := ⟨@IScalar.shiftRight_UScalar .I16   .U8   ⟩
instance : HShiftRight Int16   UInt16  (Result Int16)   := ⟨@IScalar.shiftRight_UScalar .I16   .U16  ⟩
instance : HShiftRight Int16   UInt32  (Result Int16)   := ⟨@IScalar.shiftRight_UScalar .I16   .U32  ⟩
instance : HShiftRight Int16   UInt64  (Result Int16)   := ⟨@IScalar.shiftRight_UScalar .I16   .U64  ⟩
instance : HShiftRight Int16   UInt128 (Result Int16)   := ⟨@IScalar.shiftRight_UScalar .I16   .U128 ⟩
instance : HShiftRight Int16   USize   (Result Int16)   := ⟨@IScalar.shiftRight_UScalar .I16   .Usize⟩
instance : HShiftRight Int32   UInt8   (Result Int32)   := ⟨@IScalar.shiftRight_UScalar .I32   .U8   ⟩
instance : HShiftRight Int32   UInt16  (Result Int32)   := ⟨@IScalar.shiftRight_UScalar .I32   .U16  ⟩
instance : HShiftRight Int32   UInt32  (Result Int32)   := ⟨@IScalar.shiftRight_UScalar .I32   .U32  ⟩
instance : HShiftRight Int32   UInt64  (Result Int32)   := ⟨@IScalar.shiftRight_UScalar .I32   .U64  ⟩
instance : HShiftRight Int32   UInt128 (Result Int32)   := ⟨@IScalar.shiftRight_UScalar .I32   .U128 ⟩
instance : HShiftRight Int32   USize   (Result Int32)   := ⟨@IScalar.shiftRight_UScalar .I32   .Usize⟩
instance : HShiftRight Int64   UInt8   (Result Int64)   := ⟨@IScalar.shiftRight_UScalar .I64   .U8   ⟩
instance : HShiftRight Int64   UInt16  (Result Int64)   := ⟨@IScalar.shiftRight_UScalar .I64   .U16  ⟩
instance : HShiftRight Int64   UInt32  (Result Int64)   := ⟨@IScalar.shiftRight_UScalar .I64   .U32  ⟩
instance : HShiftRight Int64   UInt64  (Result Int64)   := ⟨@IScalar.shiftRight_UScalar .I64   .U64  ⟩
instance : HShiftRight Int64   UInt128 (Result Int64)   := ⟨@IScalar.shiftRight_UScalar .I64   .U128 ⟩
instance : HShiftRight Int64   USize   (Result Int64)   := ⟨@IScalar.shiftRight_UScalar .I64   .Usize⟩
instance : HShiftRight Int128  UInt8   (Result Int128)  := ⟨@IScalar.shiftRight_UScalar .I128  .U8   ⟩
instance : HShiftRight Int128  UInt16  (Result Int128)  := ⟨@IScalar.shiftRight_UScalar .I128  .U16  ⟩
instance : HShiftRight Int128  UInt32  (Result Int128)  := ⟨@IScalar.shiftRight_UScalar .I128  .U32  ⟩
instance : HShiftRight Int128  UInt64  (Result Int128)  := ⟨@IScalar.shiftRight_UScalar .I128  .U64  ⟩
instance : HShiftRight Int128  UInt128 (Result Int128)  := ⟨@IScalar.shiftRight_UScalar .I128  .U128 ⟩
instance : HShiftRight Int128  USize   (Result Int128)  := ⟨@IScalar.shiftRight_UScalar .I128  .Usize⟩
instance : HShiftRight ISize   UInt8   (Result ISize)   := ⟨@IScalar.shiftRight_UScalar .Isize .U8   ⟩
instance : HShiftRight ISize   UInt16  (Result ISize)   := ⟨@IScalar.shiftRight_UScalar .Isize .U16  ⟩
instance : HShiftRight ISize   UInt32  (Result ISize)   := ⟨@IScalar.shiftRight_UScalar .Isize .U32  ⟩
instance : HShiftRight ISize   UInt64  (Result ISize)   := ⟨@IScalar.shiftRight_UScalar .Isize .U64  ⟩
instance : HShiftRight ISize   UInt128 (Result ISize)   := ⟨@IScalar.shiftRight_UScalar .Isize .U128 ⟩
instance : HShiftRight ISize   USize   (Result ISize)   := ⟨@IScalar.shiftRight_UScalar .Isize .Usize⟩

-- I × I
instance : HShiftRight Int8    Int8    (Result Int8)    := ⟨@IScalar.shiftRight_IScalar .I8    .I8   ⟩
instance : HShiftRight Int8    Int16   (Result Int8)    := ⟨@IScalar.shiftRight_IScalar .I8    .I16  ⟩
instance : HShiftRight Int8    Int32   (Result Int8)    := ⟨@IScalar.shiftRight_IScalar .I8    .I32  ⟩
instance : HShiftRight Int8    Int64   (Result Int8)    := ⟨@IScalar.shiftRight_IScalar .I8    .I64  ⟩
instance : HShiftRight Int8    Int128  (Result Int8)    := ⟨@IScalar.shiftRight_IScalar .I8    .I128 ⟩
instance : HShiftRight Int8    ISize   (Result Int8)    := ⟨@IScalar.shiftRight_IScalar .I8    .Isize⟩
instance : HShiftRight Int16   Int8    (Result Int16)   := ⟨@IScalar.shiftRight_IScalar .I16   .I8   ⟩
instance : HShiftRight Int16   Int16   (Result Int16)   := ⟨@IScalar.shiftRight_IScalar .I16   .I16  ⟩
instance : HShiftRight Int16   Int32   (Result Int16)   := ⟨@IScalar.shiftRight_IScalar .I16   .I32  ⟩
instance : HShiftRight Int16   Int64   (Result Int16)   := ⟨@IScalar.shiftRight_IScalar .I16   .I64  ⟩
instance : HShiftRight Int16   Int128  (Result Int16)   := ⟨@IScalar.shiftRight_IScalar .I16   .I128 ⟩
instance : HShiftRight Int16   ISize   (Result Int16)   := ⟨@IScalar.shiftRight_IScalar .I16   .Isize⟩
instance : HShiftRight Int32   Int8    (Result Int32)   := ⟨@IScalar.shiftRight_IScalar .I32   .I8   ⟩
instance : HShiftRight Int32   Int16   (Result Int32)   := ⟨@IScalar.shiftRight_IScalar .I32   .I16  ⟩
instance : HShiftRight Int32   Int32   (Result Int32)   := ⟨@IScalar.shiftRight_IScalar .I32   .I32  ⟩
instance : HShiftRight Int32   Int64   (Result Int32)   := ⟨@IScalar.shiftRight_IScalar .I32   .I64  ⟩
instance : HShiftRight Int32   Int128  (Result Int32)   := ⟨@IScalar.shiftRight_IScalar .I32   .I128 ⟩
instance : HShiftRight Int32   ISize   (Result Int32)   := ⟨@IScalar.shiftRight_IScalar .I32   .Isize⟩
instance : HShiftRight Int64   Int8    (Result Int64)   := ⟨@IScalar.shiftRight_IScalar .I64   .I8   ⟩
instance : HShiftRight Int64   Int16   (Result Int64)   := ⟨@IScalar.shiftRight_IScalar .I64   .I16  ⟩
instance : HShiftRight Int64   Int32   (Result Int64)   := ⟨@IScalar.shiftRight_IScalar .I64   .I32  ⟩
instance : HShiftRight Int64   Int64   (Result Int64)   := ⟨@IScalar.shiftRight_IScalar .I64   .I64  ⟩
instance : HShiftRight Int64   Int128  (Result Int64)   := ⟨@IScalar.shiftRight_IScalar .I64   .I128 ⟩
instance : HShiftRight Int64   ISize   (Result Int64)   := ⟨@IScalar.shiftRight_IScalar .I64   .Isize⟩
instance : HShiftRight Int128  Int8    (Result Int128)  := ⟨@IScalar.shiftRight_IScalar .I128  .I8   ⟩
instance : HShiftRight Int128  Int16   (Result Int128)  := ⟨@IScalar.shiftRight_IScalar .I128  .I16  ⟩
instance : HShiftRight Int128  Int32   (Result Int128)  := ⟨@IScalar.shiftRight_IScalar .I128  .I32  ⟩
instance : HShiftRight Int128  Int64   (Result Int128)  := ⟨@IScalar.shiftRight_IScalar .I128  .I64  ⟩
instance : HShiftRight Int128  Int128  (Result Int128)  := ⟨@IScalar.shiftRight_IScalar .I128  .I128 ⟩
instance : HShiftRight Int128  ISize   (Result Int128)  := ⟨@IScalar.shiftRight_IScalar .I128  .Isize⟩
instance : HShiftRight ISize   Int8    (Result ISize)   := ⟨@IScalar.shiftRight_IScalar .Isize .I8   ⟩
instance : HShiftRight ISize   Int16   (Result ISize)   := ⟨@IScalar.shiftRight_IScalar .Isize .I16  ⟩
instance : HShiftRight ISize   Int32   (Result ISize)   := ⟨@IScalar.shiftRight_IScalar .Isize .I32  ⟩
instance : HShiftRight ISize   Int64   (Result ISize)   := ⟨@IScalar.shiftRight_IScalar .Isize .I64  ⟩
instance : HShiftRight ISize   Int128  (Result ISize)   := ⟨@IScalar.shiftRight_IScalar .Isize .I128 ⟩
instance : HShiftRight ISize   ISize   (Result ISize)   := ⟨@IScalar.shiftRight_IScalar .Isize .Isize⟩

/-!
Bitwise and
-/
def UScalar.and {ty} (x y : UScalar ty) : UScalar ty := UScalar.ofBitVec ty (UScalar.toBitVec x &&& UScalar.toBitVec y)

def IScalar.and {ty} (x y : IScalar ty) : IScalar ty := IScalar.ofBitVec ty (IScalar.toBitVec x &&& IScalar.toBitVec y)

instance {ty} : HAnd (UScalar ty) (UScalar ty) (UScalar ty) where
  hAnd x y := UScalar.and x y

instance {ty} : HAnd (IScalar ty) (IScalar ty) (IScalar ty) where
  hAnd x y := IScalar.and x y

/-!
Bitwise or
-/
def UScalar.or {ty} (x y : UScalar ty) : UScalar ty := UScalar.ofBitVec ty (UScalar.toBitVec x ||| UScalar.toBitVec y)

def IScalar.or {ty} (x y : IScalar ty) : IScalar ty := IScalar.ofBitVec ty (IScalar.toBitVec x ||| IScalar.toBitVec y)

instance {ty} : HOr (UScalar ty) (UScalar ty) (UScalar ty) where
  hOr x y := UScalar.or x y

instance {ty} : HOr (IScalar ty) (IScalar ty) (IScalar ty) where
  hOr x y := IScalar.or x y

/-!
Xor
-/
def UScalar.xor {ty} (x y : UScalar ty) : UScalar ty := UScalar.ofBitVec ty (UScalar.toBitVec x ^^^ UScalar.toBitVec y)

def IScalar.xor {ty} (x y : IScalar ty) : IScalar ty := IScalar.ofBitVec ty (IScalar.toBitVec x ^^^ IScalar.toBitVec y)

instance {ty} : HXor (UScalar ty) (UScalar ty) (UScalar ty) where
  hXor x y := UScalar.xor x y

instance {ty} : HXor (IScalar ty) (IScalar ty) (IScalar ty) where
  hXor x y := IScalar.xor x y

/-!
Not
-/
def UScalar.not {ty} (x : UScalar ty) : UScalar ty := UScalar.ofBitVec ty (~~~(UScalar.toBitVec x))

def IScalar.not {ty} (x : IScalar ty) : IScalar ty := IScalar.ofBitVec ty (~~~(IScalar.toBitVec x))

instance {ty} : Complement (UScalar ty) where
  complement x := UScalar.not x

instance {ty} : Complement (IScalar ty) where
  complement x := IScalar.not x

/-!
# Bitwise Operations: Theorems
-/


/-!
## Bit shifts
-/

theorem UScalar.ShiftRight_spec {ty0 ty1} (x : UScalar ty0) (y : UScalar ty1)
  (hy : y.toNat < ty0.numBits) :
  (x >>> y) ⦃ z =>
    z.toNat = x.toNat >>> y.toNat ∧
    UScalar.toBitVec z = UScalar.toBitVec x >>> y.toNat ⦄
  := by
  simp only [spec_ok, HShiftRight.hShiftRight, shiftRight_UScalar, shiftRight, hy, reduceIte]
  simp only [UScalar.ofBitVec_toNat, UScalar.ofBitVec_toBitVec]
  simp only [UScalar.toNat, toBitVec_toNat, BitVec.ushiftRight_eq, Nat.instShiftRight,
    BitVec.toNat_ushiftRight, and_true, Nat.shiftRight_eq]

uscalar @[step] theorem «%S».ShiftRight_spec {ty1} (x : «%S») (y : UScalar ty1) (hy : y.toNat < %BitWidth) :
  UScalar.shiftRight_UScalar x y ⦃ (z : «%S») => z.toNat = x.toNat >>> y.toNat ∧ z.toBitVec = x.toBitVec >>> y.toNat ⦄
  := by apply UScalar.ShiftRight_spec; simp [*]

theorem UScalar.ShiftRight_IScalar_spec {ty0 ty1} (x : UScalar ty0) (y : IScalar ty1)
  (hy0 : 0 ≤ y.toInt) (hy1 : y.toInt < ty0.numBits) :
  (x >>> y) ⦃ z => z.toNat = x.toNat >>> y.toNat ∧ UScalar.toBitVec z = UScalar.toBitVec x >>> y.toNat ⦄
  := by
  have hy1 : y.toNat < ty0.numBits := by scalar_tac
  simp only [spec_ok, HShiftRight.hShiftRight, shiftRight_IScalar, shiftRight, hy1, reduceIte]
  simp only [UScalar.ofBitVec_toNat, UScalar.ofBitVec_toBitVec]
  simp only [UScalar.toNat, IScalar.toNat, toBitVec_toNat, BitVec.ushiftRight_eq, Nat.instShiftRight,
    BitVec.toNat_ushiftRight, and_true, Nat.shiftRight_eq]

uscalar @[step] theorem «%S».ShiftRight_IScalar_spec {ty1} (x : «%S») (y : IScalar ty1) (hy0 : 0 ≤ y.toInt) (hy : y.toInt < %BitWidth) :
  UScalar.shiftRight_IScalar x y ⦃ (z : «%S») => z.toNat = x.toNat >>> y.toNat ∧ z.toBitVec = x.toBitVec >>> y.toNat ⦄
  := by apply UScalar.ShiftRight_IScalar_spec <;> simp [*]

theorem UScalar.ShiftLeft_spec {ty0 ty1} (x : UScalar ty0) (y : UScalar ty1) (size : Nat)
  (hy : y.toNat < ty0.numBits) (hsize : size = UScalar.size ty0) :
  (x <<< y) ⦃ z =>
  z.toNat = (x.toNat <<< y.toNat) % size ∧
  UScalar.toBitVec z = UScalar.toBitVec x <<< y.toNat ⦄
  := by
  simp only [spec_ok, HShiftLeft.hShiftLeft, shiftLeft_UScalar, shiftLeft, hy, reduceIte, hsize, UScalar.size]
  simp only [UScalar.ofBitVec_toNat, UScalar.ofBitVec_toBitVec]
  simp only [UScalar.toNat, toBitVec_toNat, BitVec.shiftLeft_eq, BitVec.toNat_shiftLeft,
    ShiftLeft.shiftLeft, Nat.shiftLeft_eq', and_true]

uscalar @[step] theorem «%S».ShiftLeft_spec {ty1} (x : «%S») (y : UScalar ty1) (hy : y.toNat < %BitWidth) :
  UScalar.shiftLeft_UScalar x y ⦃ (z : «%S») => z.toNat = (x.toNat <<< y.toNat) % «%S».size ∧ z.toBitVec = x.toBitVec <<< y.toNat ⦄
  := by apply UScalar.ShiftLeft_spec <;> simp [*]

theorem UScalar.ShiftLeft_IScalar_spec {ty0 ty1} (x : UScalar ty0) (y : IScalar ty1) (size : Nat)
  (hy0 : 0 ≤ y.toInt) (hy1 : y.toInt < ty0.numBits) (hsize : size = UScalar.size ty0) :
  (x <<< y) ⦃ z =>
  z.toNat = (x.toNat <<< y.toNat) % size ∧
  UScalar.toBitVec z = UScalar.toBitVec x <<< y.toNat ⦄
  := by
  have hy1 : y.toNat < ty0.numBits := by scalar_tac
  simp only [spec_ok, HShiftLeft.hShiftLeft, shiftLeft_IScalar, shiftLeft, hy1, reduceIte, hsize,
    UScalar.size]
  simp only [UScalar.ofBitVec_toNat, UScalar.ofBitVec_toBitVec]
  simp only [UScalar.toNat, IScalar.toNat, toBitVec_toNat, BitVec.shiftLeft_eq,
    BitVec.toNat_shiftLeft, ShiftLeft.shiftLeft, Nat.shiftLeft_eq', and_true]

uscalar @[step] theorem «%S».ShiftLeft_IScalar_spec {ty1} (x : «%S») (y : IScalar ty1) (hy0 : 0 ≤ y.toInt) (hy : y.toInt < %BitWidth) :
  UScalar.shiftLeft_IScalar x y ⦃ (z : «%S») => z.toNat = (x.toNat <<< y.toNat) % «%S».size ∧ z.toBitVec = x.toBitVec <<< y.toNat ⦄
  := by apply UScalar.ShiftLeft_IScalar_spec <;> simp [*]

/-!
## Bitwise And, Or
-/

@[step]
theorem UScalar.and_spec {ty} (x y : UScalar ty) :
  lift (x &&& y) ⦃ z => z.toNat = (x &&& y).toNat ∧ UScalar.toBitVec z = UScalar.toBitVec x &&& UScalar.toBitVec y ⦄ := by
  simp [lift]; cases ty <;> rfl

@[step]
theorem UScalar.or_spec {ty} (x y : UScalar ty) :
  lift (x ||| y) ⦃ z => z.toNat = (x ||| y).toNat ∧ UScalar.toBitVec z = UScalar.toBitVec x ||| UScalar.toBitVec y ⦄ := by
  simp [lift]; cases ty <;> rfl

@[step]
theorem UScalar.xor_spec {ty} (x y : UScalar ty) :
  lift (x ^^^ y) ⦃ z => z.toNat = (x ^^^ y).toNat ∧ UScalar.toBitVec z = UScalar.toBitVec x ^^^ UScalar.toBitVec y ⦄ := by
  simp [lift]; cases ty <;> rfl

@[step]
theorem IScalar.and_spec {ty} (x y : IScalar ty) :
  lift (x &&& y) ⦃ z => z.toInt = (x &&& y).toInt ∧ IScalar.toBitVec z = IScalar.toBitVec x &&& IScalar.toBitVec y ⦄ := by
  simp [lift]; cases ty <;> rfl

@[step]
theorem IScalar.or_spec {ty} (x y : IScalar ty) :
  lift (x ||| y) ⦃ z => z.toInt = (x ||| y).toInt ∧ IScalar.toBitVec z = IScalar.toBitVec x ||| IScalar.toBitVec y ⦄ := by
  simp [lift]; cases ty <;> rfl

@[step]
theorem IScalar.xor_spec {ty} (x y : IScalar ty) :
  lift (x ^^^ y) ⦃ z => z.toInt = (x ^^^ y).toInt ∧ IScalar.toBitVec z = IScalar.toBitVec x ^^^ IScalar.toBitVec y ⦄ := by
  simp [lift]; cases ty <;> rfl

@[step]
theorem UScalar.not_spec {ty} (x : UScalar ty) :
  lift (~~~x) ⦃ z => z = ~~~x ⦄ := by
  simp [lift]

@[step]
theorem IScalar.not_spec {ty} (x : IScalar ty) :
  lift (~~~x) ⦃ z => z = ~~~x ⦄ := by
  simp [lift]

@[simp, bvify, grind =, agrind =] theorem UScalar.bv_and {ty} (x y : UScalar ty) : UScalar.toBitVec (x &&& y) = UScalar.toBitVec x &&& UScalar.toBitVec y := by cases ty <;> rfl
@[simp, bvify, grind =, agrind =] theorem UScalar.bv_or {ty} (x y : UScalar ty) : UScalar.toBitVec (x ||| y) = UScalar.toBitVec x ||| UScalar.toBitVec y := by cases ty <;> rfl
@[simp, bvify, grind =, agrind =] theorem UScalar.bv_xor {ty} (x y : UScalar ty) : UScalar.toBitVec (x ^^^ y) = UScalar.toBitVec x ^^^ UScalar.toBitVec y := by cases ty <;> rfl
@[simp, bvify, grind =, agrind =] theorem UScalar.bv_not {ty} (x : UScalar ty) : UScalar.toBitVec (~~~x) = ~~~(UScalar.toBitVec x) := by cases ty <;> rfl
@[simp, bvify, grind =, agrind =] theorem IScalar.bv_and {ty} (x y : IScalar ty) : IScalar.toBitVec (x &&& y) = IScalar.toBitVec x &&& IScalar.toBitVec y := by cases ty <;> rfl
@[simp, bvify, grind =, agrind =] theorem IScalar.bv_or {ty} (x y : IScalar ty) : IScalar.toBitVec (x ||| y) = IScalar.toBitVec x ||| IScalar.toBitVec y := by cases ty <;> rfl
@[simp, bvify, grind =, agrind =] theorem IScalar.bv_xor {ty} (x y : IScalar ty) : IScalar.toBitVec (x ^^^ y) = IScalar.toBitVec x ^^^ IScalar.toBitVec y := by cases ty <;> rfl
@[simp, bvify, grind =, agrind =] theorem IScalar.bv_not {ty} (x : IScalar ty) : IScalar.toBitVec (~~~x) = ~~~(IScalar.toBitVec x) := by cases ty <;> rfl

@[simp, scalar_tac_simps, grind =, agrind =] theorem UScalar.val_and {ty} (x y : UScalar ty) : (x &&& y).toNat = x.toNat &&& y.toNat := by cases ty <;> rfl
@[simp, scalar_tac_simps, grind =, agrind =] theorem UScalar.val_or {ty} (x y : UScalar ty) : (x ||| y).toNat = x.toNat ||| y.toNat := by cases ty <;> rfl
@[simp, scalar_tac_simps, grind =, agrind =] theorem UScalar.val_xor {ty} (x y : UScalar ty) : (x ^^^ y).toNat = x.toNat ^^^ y.toNat := by cases ty <;> rfl

end Aeneas.Std
