import Lean
import Lean.Meta.Tactic.Simp
import Aeneas.Std.Core.Core
import Aeneas.Tactic.Step.Init
import Aeneas.Tactic.Solver.ScalarTac.ScalarTac
import Aeneas.Tactic.Conv.Bvify.Init
import Aeneas.Data.Nat
import Aeneas.Data.Int
import Aeneas.Tactic.Simp.SimpLists.Init
import Aeneas.Std.Scalar.Int128
import Aeneas.Std.Scalar.Elab

namespace Aeneas

namespace Std

-- Deactivate the warnings which appear when we use `#assert`
set_option linter.hashCommand false

/-!
# Machine Integers

Because they tend to behave quite differently, we have two classes of machine integers: one for
signed integers, and another for unsigned integers. Inside of each class, we factor out definitions.
-/

open Result Error

/-- Kinds of unsigned integers -/
inductive UScalarTy where
| Usize
| U8
| U16
| U32
| U64
| U128

/-- Kinds of signed integers -/
inductive IScalarTy where
| Isize
| I8
| I16
| I32
| I64
| I128

def UScalarTy.numBits (ty : UScalarTy) : Nat :=
  match ty with
  | Usize => System.Platform.numBits
  | U8 => 8
  | U16 => 16
  | U32 => 32
  | U64 => 64
  | U128 => 128

def IScalarTy.numBits (ty : IScalarTy) : Nat :=
  match ty with
  | Isize => System.Platform.numBits
  | I8 => 8
  | I16 => 16
  | I32 => 32
  | I64 => 64
  | I128 => 128

/-!
# `UScalar` and `IScalar` — abbrevs to official Lean integer types
-/

/-- Unsigned machine integer — reduces to the official Lean type for each width. -/
abbrev UScalar : UScalarTy → Type
  | .U8    => UInt8
  | .U16   => UInt16
  | .U32   => UInt32
  | .U64   => UInt64
  | .U128  => UInt128
  | .Usize => USize

/-- Signed machine integer — reduces to the official Lean type for each width. -/
abbrev IScalar : IScalarTy → Type
  | .I8    => Int8
  | .I16   => Int16
  | .I32   => Int32
  | .I64   => Int64
  | .I128  => Int128
  | .Isize => ISize

/-!
## Key accessor functions

Because `UScalar ty` reduces to different types for each `ty`, standard dot-notation
`x.toNat` only works in contexts where `ty` is known.  For polymorphic code we define
`UScalar.toNat` / `IScalar.toInt` that dispatch by matching on `ty`.
-/

/-- Extract the value of an unsigned scalar as a natural number. -/
@[reducible] def UScalar.toNat {ty : UScalarTy} (x : UScalar ty) : Nat :=
  match ty with
  | .U8    => UInt8.toNat x
  | .U16   => UInt16.toNat x
  | .U32   => UInt32.toNat x
  | .U64   => UInt64.toNat x
  | .U128  => UInt128.toNat x
  | .Usize => USize.toNat x

/-- Extract the value of a signed scalar as an integer. -/
@[reducible] def IScalar.toInt {ty : IScalarTy} (x : IScalar ty) : Int :=
  match ty with
  | .I8    => Int8.toInt x
  | .I16   => Int16.toInt x
  | .I32   => Int32.toInt x
  | .I64   => Int64.toInt x
  | .I128  => Int128.toInt x
  | .Isize => ISize.toInt x

/-- Construct an unsigned scalar from its `BitVec` representation. -/
@[reducible] def UScalar.ofBitVec (ty : UScalarTy) (bv : BitVec ty.numBits) : UScalar ty :=
  match ty with
  | .U8    => UInt8.ofBitVec bv
  | .U16   => UInt16.ofBitVec bv
  | .U32   => UInt32.ofBitVec bv
  | .U64   => UInt64.ofBitVec bv
  | .U128  => UInt128.ofBitVec bv
  | .Usize => USize.ofBitVec bv

/-- Construct a signed scalar from its `BitVec` representation. -/
@[reducible] def IScalar.ofBitVec (ty : IScalarTy) (bv : BitVec ty.numBits) : IScalar ty :=
  match ty with
  | .I8    => Int8.ofBitVec bv
  | .I16   => Int16.ofBitVec bv
  | .I32   => Int32.ofBitVec bv
  | .I64   => Int64.ofBitVec bv
  | .I128  => Int128.ofBitVec bv
  | .Isize => ISize.ofBitVec bv

/-- Extract the `BitVec` representation of an unsigned scalar (polymorphic form). -/
@[reducible] def UScalar.toBitVec {ty : UScalarTy} (x : UScalar ty) : BitVec ty.numBits :=
  match ty with
  | .U8    => UInt8.toBitVec x
  | .U16   => UInt16.toBitVec x
  | .U32   => UInt32.toBitVec x
  | .U64   => UInt64.toBitVec x
  | .U128  => UInt128.toBitVec x
  | .Usize => USize.toBitVec x

/-- Extract the `BitVec` representation of a signed scalar (polymorphic form). -/
@[reducible] def IScalar.toBitVec {ty : IScalarTy} (x : IScalar ty) : BitVec ty.numBits :=
  match ty with
  | .I8    => Int8.toBitVec x
  | .I16   => Int16.toBitVec x
  | .I32   => Int32.toBitVec x
  | .I64   => Int64.toBitVec x
  | .I128  => Int128.toBitVec x
  | .Isize => ISize.toBitVec x

/-!
# Bounds, Size

**Remark:** we mark most constants as irreducible because otherwise it leads to issues
when using tactics like `assumption`: it often happens that unification attempts to reduce
complex expressions (for instance by trying to reduce an expression like `2^128`, which
is extremely expensive).
-/

irreducible_def UScalar.max (ty : UScalarTy) : Nat := 2^ty.numBits-1
irreducible_def IScalar.min (ty : IScalarTy) : Int := -2^(ty.numBits - 1)
irreducible_def IScalar.max (ty : IScalarTy) : Int := 2^(ty.numBits - 1)-1

irreducible_def UScalar.size (ty : UScalarTy) : Nat := 2^ty.numBits
irreducible_def IScalar.size (ty : IScalarTy) : Int := 2^ty.numBits

/-! ## Num Bits -/
irreducible_def U8.numBits    : Nat := UScalarTy.U8.numBits
irreducible_def U16.numBits   : Nat := UScalarTy.U16.numBits
irreducible_def U32.numBits   : Nat := UScalarTy.U32.numBits
irreducible_def U64.numBits   : Nat := UScalarTy.U64.numBits
irreducible_def U128.numBits  : Nat := UScalarTy.U128.numBits
irreducible_def Usize.numBits : Nat := UScalarTy.Usize.numBits

irreducible_def I8.numBits    : Nat := IScalarTy.I8.numBits
irreducible_def I16.numBits   : Nat := IScalarTy.I16.numBits
irreducible_def I32.numBits   : Nat := IScalarTy.I32.numBits
irreducible_def I64.numBits   : Nat := IScalarTy.I64.numBits
irreducible_def I128.numBits  : Nat := IScalarTy.I128.numBits
irreducible_def Isize.numBits : Nat := IScalarTy.Isize.numBits

/-! ## Bounds -/
irreducible_def U8.max    : Nat := 2^U8.numBits - 1
irreducible_def U16.max   : Nat := 2^U16.numBits - 1
irreducible_def U32.max   : Nat := 2^U32.numBits - 1
irreducible_def U64.max   : Nat := 2^U64.numBits - 1
irreducible_def U128.max  : Nat := 2^U128.numBits - 1
irreducible_def Usize.max : Nat := 2^Usize.numBits - 1

irreducible_def I8.min    : Int := -2^(I8.numBits - 1)
irreducible_def I8.max    : Int := 2^(I8.numBits - 1) - 1
irreducible_def I16.min   : Int := -2^(I16.numBits - 1)
irreducible_def I16.max   : Int := 2^(I16.numBits - 1) - 1
irreducible_def I32.min   : Int := -2^(I32.numBits - 1)
irreducible_def I32.max   : Int := 2^(I32.numBits - 1) - 1
irreducible_def I64.min   : Int := -2^(I64.numBits - 1)
irreducible_def I64.max   : Int := 2^(I64.numBits - 1) - 1
irreducible_def I128.min  : Int := -2^(I128.numBits - 1)
irreducible_def I128.max  : Int := 2^(I128.numBits - 1) - 1
irreducible_def Isize.min : Int := -2^(Isize.numBits - 1)
irreducible_def Isize.max : Int := 2^(Isize.numBits - 1) - 1

/-! ## Size -/
irreducible_def U8.size    : Nat := 2^U8.numBits
irreducible_def U16.size   : Nat := 2^U16.numBits
irreducible_def U32.size   : Nat := 2^U32.numBits
irreducible_def U64.size   : Nat := 2^U64.numBits
irreducible_def U128.size  : Nat := 2^U128.numBits
irreducible_def Usize.size : Nat := 2^Usize.numBits

irreducible_def I8.size    : Nat := 2^I8.numBits
irreducible_def I16.size   : Nat := 2^I16.numBits
irreducible_def I32.size   : Nat := 2^I32.numBits
irreducible_def I64.size   : Nat := 2^I64.numBits
irreducible_def I128.size  : Nat := 2^I128.numBits
irreducible_def Isize.size : Nat := 2^Isize.numBits

/-! ## "Reduced" Constants -/
/-! ### Size -/
def I8.rSize   : Int := 256
def I16.rSize  : Int := 65536
def I32.rSize  : Int := 4294967296
def I64.rSize  : Int := 18446744073709551616
def I128.rSize : Int := 340282366920938463463374607431768211456

def U8.rSize   : Nat := 256
def U16.rSize  : Nat := 65536
def U32.rSize  : Nat := 4294967296
def U64.rSize  : Nat := 18446744073709551616
def U128.rSize : Nat := 340282366920938463463374607431768211456

/-! ### Bounds -/
def U8.rMax   : Nat := 255
def U16.rMax  : Nat := 65535
def U32.rMax  : Nat := 4294967295
def U64.rMax  : Nat := 18446744073709551615
def U128.rMax : Nat := 340282366920938463463374607431768211455
def Usize.rMax : Nat := 2^System.Platform.numBits-1

def I8.rMin   : Int := -128
def I8.rMax   : Int := 127
def I16.rMin  : Int := -32768
def I16.rMax  : Int := 32767
def I32.rMin  : Int := -2147483648
def I32.rMax  : Int := 2147483647
def I64.rMin  : Int := -9223372036854775808
def I64.rMax  : Int := 9223372036854775807
def I128.rMin : Int := -170141183460469231731687303715884105728
def I128.rMax : Int := 170141183460469231731687303715884105727
def Isize.rMin : Int := -2^(System.Platform.numBits - 1)
def Isize.rMax : Int := 2^(System.Platform.numBits - 1)-1

def UScalar.rMax (ty : UScalarTy) : Nat :=
  match ty with
  | .Usize => Usize.rMax
  | .U8    => U8.rMax
  | .U16   => U16.rMax
  | .U32   => U32.rMax
  | .U64   => U64.rMax
  | .U128  => U128.rMax

def IScalar.rMin (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => Isize.rMin
  | .I8    => I8.rMin
  | .I16   => I16.rMin
  | .I32   => I32.rMin
  | .I64   => I64.rMin
  | .I128  => I128.rMin

def IScalar.rMax (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => Isize.rMax
  | .I8    => I8.rMax
  | .I16   => I16.rMax
  | .I32   => I32.rMax
  | .I64   => I64.rMax
  | .I128  => I128.rMax

/-! # Theorems -/
theorem UScalarTy.numBits_nonzero (ty : UScalarTy) : ty.numBits ≠ 0 := by
  cases ty <;> simp [numBits]
  cases System.Platform.numBits_eq <;> simp_all

theorem IScalarTy.numBits_nonzero (ty : IScalarTy) : ty.numBits ≠ 0 := by
  cases ty <;> simp [numBits]
  cases System.Platform.numBits_eq <;> simp_all

@[defeq, simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem UScalarTy.U8_numBits_eq    : UScalarTy.U8.numBits    = 8 := by rfl
@[defeq, simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem UScalarTy.U16_numBits_eq   : UScalarTy.U16.numBits   = 16 := by rfl
@[defeq, simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem UScalarTy.U32_numBits_eq   : UScalarTy.U32.numBits   = 32 := by rfl
@[defeq, simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem UScalarTy.U64_numBits_eq   : UScalarTy.U64.numBits   = 64 := by rfl
@[defeq, simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem UScalarTy.U128_numBits_eq  : UScalarTy.U128.numBits  = 128 := by rfl
@[defeq, simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem UScalarTy.Usize_numBits_eq : UScalarTy.Usize.numBits = System.Platform.numBits := by rfl

@[defeq, simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem IScalarTy.I8_numBits_eq    : IScalarTy.I8.numBits    = 8 := by rfl
@[defeq, simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem IScalarTy.I16_numBits_eq   : IScalarTy.I16.numBits   = 16 := by rfl
@[defeq, simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem IScalarTy.I32_numBits_eq   : IScalarTy.I32.numBits   = 32 := by rfl
@[defeq, simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem IScalarTy.I64_numBits_eq   : IScalarTy.I64.numBits   = 64 := by rfl
@[defeq, simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem IScalarTy.I128_numBits_eq  : IScalarTy.I128.numBits  = 128 := by rfl
@[defeq, simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem IScalarTy.Isize_numBits_eq : IScalarTy.Isize.numBits = System.Platform.numBits := by rfl

@[simp, grind =, agrind =] theorem UScalar.max_UScalarTy_U8_eq    : UScalar.max .U8 = U8.max := by simp [UScalar.max, U8.max, U8.numBits]
@[simp, grind =, agrind =] theorem UScalar.max_UScalarTy_U16_eq   : UScalar.max .U16 = U16.max := by simp [UScalar.max, U16.max, U16.numBits]
@[simp, grind =, agrind =] theorem UScalar.max_UScalarTy_U32_eq   : UScalar.max .U32 = U32.max := by simp [UScalar.max, U32.max, U32.numBits]
@[simp, grind =, agrind =] theorem UScalar.max_UScalarTy_U64_eq   : UScalar.max .U64 = U64.max := by simp [UScalar.max, U64.max, U64.numBits]
@[simp, grind =, agrind =] theorem UScalar.max_UScalarTy_U128_eq  : UScalar.max .U128 = U128.max := by simp [UScalar.max, U128.max, U128.numBits]
@[scalar_tac_simps, grind =, agrind =] theorem UScalar.max_USize_eq : UScalar.max .Usize = Usize.max := by simp [UScalar.max, Usize.max, Usize.numBits]

@[simp, grind =, agrind =] theorem IScalar.min_IScalarTy_I8_eq    : IScalar.min .I8 = I8.min := by simp [IScalar.min, I8.min, I8.numBits]
@[simp, grind =, agrind =] theorem IScalar.max_IScalarTy_I8_eq    : IScalar.max .I8 = I8.max := by simp [IScalar.max, I8.max, I8.numBits]
@[simp, grind =, agrind =] theorem IScalar.min_IScalarTy_I16_eq   : IScalar.min .I16 = I16.min := by simp [IScalar.min, I16.min, I16.numBits]
@[simp, grind =, agrind =] theorem IScalar.max_IScalarTy_I16_eq   : IScalar.max .I16 = I16.max := by simp [IScalar.max, I16.max, I16.numBits]
@[simp, grind =, agrind =] theorem IScalar.min_IScalarTy_I32_eq   : IScalar.min .I32 = I32.min := by simp [IScalar.min, I32.min, I32.numBits]
@[simp, grind =, agrind =] theorem IScalar.max_IScalarTy_I32_eq   : IScalar.max .I32 = I32.max := by simp [IScalar.max, I32.max, I32.numBits]
@[simp, grind =, agrind =] theorem IScalar.min_IScalarTy_I64_eq   : IScalar.min .I64 = I64.min := by simp [IScalar.min, I64.min, I64.numBits]
@[simp, grind =, agrind =] theorem IScalar.max_IScalarTy_I64_eq   : IScalar.max .I64 = I64.max := by simp [IScalar.max, I64.max, I64.numBits]
@[simp, grind =, agrind =] theorem IScalar.min_IScalarTy_I128_eq  : IScalar.min .I128 = I128.min := by simp [IScalar.min, I128.min, I128.numBits]
@[simp, grind =, agrind =] theorem IScalar.max_IScalarTy_I128_eq  : IScalar.max .I128 = I128.max := by simp [IScalar.max, I128.max, I128.numBits]
@[scalar_tac_simps, grind =, agrind =] theorem IScalar.min_ISize_eq : IScalar.min .Isize = Isize.min := by simp [IScalar.min, Isize.min, Isize.numBits]
@[scalar_tac_simps, grind =, agrind =] theorem IScalar.max_ISize_eq : IScalar.max .Isize = Isize.max := by simp [IScalar.max, Isize.max, Isize.numBits]

@[scalar_tac_simps, grind =, agrind =] theorem U8.max_eq    : U8.max = 255 := by simp [U8.max, U8.numBits]
@[scalar_tac_simps, grind =, agrind =] theorem U16.max_eq   : U16.max = 65535 := by simp [U16.max, U16.numBits]
@[scalar_tac_simps, grind =, agrind =] theorem U32.max_eq   : U32.max = 4294967295 := by simp [U32.max, U32.numBits]
@[scalar_tac_simps, grind =, agrind =] theorem U64.max_eq   : U64.max = 18446744073709551615 := by simp [U64.max, U64.numBits]
@[scalar_tac_simps, grind =, agrind =] theorem U128.max_eq  : U128.max = 340282366920938463463374607431768211455 := by simp [U128.max, U128.numBits]

@[scalar_tac_simps, grind =, agrind =] theorem I8.min_eq    : I8.min = -128 := by simp [I8.min, I8.numBits]
@[scalar_tac_simps, grind =, agrind =] theorem I8.max_eq    : I8.max = 127 := by simp [I8.max, I8.numBits]
@[scalar_tac_simps, grind =, agrind =] theorem I16.min_eq   : I16.min = -32768 := by simp [I16.min, I16.numBits]
@[scalar_tac_simps, grind =, agrind =] theorem I16.max_eq   : I16.max = 32767 := by simp [I16.max, I16.numBits]
@[scalar_tac_simps, grind =, agrind =] theorem I32.min_eq   : I32.min = -2147483648 := by simp [I32.min, I32.numBits]
@[scalar_tac_simps, grind =, agrind =] theorem I32.max_eq   : I32.max = 2147483647 := by simp [I32.max, I32.numBits]
@[scalar_tac_simps, grind =, agrind =] theorem I64.min_eq   : I64.min = -9223372036854775808 := by simp [I64.min, I64.numBits]
@[scalar_tac_simps, grind =, agrind =] theorem I64.max_eq   : I64.max = 9223372036854775807 := by simp [I64.max, I64.numBits]
@[scalar_tac_simps, grind =, agrind =] theorem I128.min_eq  : I128.min = -170141183460469231731687303715884105728 := by simp [I128.min, I128.numBits]
@[scalar_tac_simps, grind =, agrind =] theorem I128.max_eq  : I128.max = 170141183460469231731687303715884105727 := by simp [I128.max, I128.numBits]

local syntax "simp_bounds" : tactic
local macro_rules
| `(tactic|simp_bounds) =>
  `(tactic|
      simp [
      UScalar.rMax, UScalar.max,
      Usize.rMax, Usize.rMax, Usize.max,
      U8.rMax, U8.max, U16.rMax, U16.max, U32.rMax, U32.max,
      U64.rMax, U64.max, U128.rMax, U128.max,
      U8.numBits, U16.numBits, U32.numBits, U64.numBits, U128.numBits, Usize.numBits,
      UScalar.size, U8.size, U16.size, U32.size, U64.size, U128.size, Usize.size,
      IScalar.rMax, IScalar.max,
      IScalar.rMin, IScalar.min,
      Isize.rMax, Isize.rMax, Isize.max,
      I8.rMax, I8.max, I16.rMax, I16.max, I32.rMax, I32.max,
      I64.rMax, I64.max, I128.rMax, I128.max,
      Isize.rMin, Isize.rMin, Isize.min,
      I8.rMin, I8.min, I16.rMin, I16.min, I32.rMin, I32.min,
      I64.rMin, I64.min, I128.rMin, I128.min,
      I8.numBits, I16.numBits, I32.numBits, I64.numBits, I128.numBits, Isize.numBits,
      IScalar.size, I8.size, I16.size, I32.size, I64.size, I128.size, Isize.size])

theorem Usize.bounds_eq :
  Usize.max = U32.max ∨ Usize.max = U64.max := by
  simp [Usize.max, Usize.numBits]
  cases System.Platform.numBits_eq <;>
  simp [*] <;>
  simp_bounds

grind_pattern Usize.bounds_eq => Usize.max
grind_pattern [agrind] Usize.bounds_eq => Usize.max

private abbrev _usizeMaxPowTrigger := 2^System.Platform.numBits

@[scalar_tac _usizeMaxPowTrigger]
theorem Usize.max_lt_pow : Usize.max < 2^System.Platform.numBits := by
  simp [Usize.max, Usize.numBits]

theorem Isize.bounds_eq :
  (Isize.min = I32.min ∧ Isize.max = I32.max)
  ∨ (Isize.min = I64.min ∧ Isize.max = I64.max) := by
  simp [Isize.min, Isize.max, Isize.numBits]
  cases System.Platform.numBits_eq <;>
  simp [*] <;> simp [*, I32.min, I32.numBits, I32.max, I64.min, I64.numBits, I64.max]

grind_pattern Isize.bounds_eq => Isize.max
grind_pattern Isize.bounds_eq => Isize.min
grind_pattern [agrind] Isize.bounds_eq => Isize.max
grind_pattern [agrind] Isize.bounds_eq => Isize.min

theorem UScalar.rMax_eq_max (ty : UScalarTy) : UScalar.rMax ty = UScalar.max ty := by
  cases ty <;>
  simp_bounds

theorem IScalar.rbound_eq_bound (ty : IScalarTy) :
  IScalar.rMin ty = IScalar.min ty ∧ IScalar.rMax ty = IScalar.max ty := by
  cases ty <;> split_conjs <;>
  simp_bounds

theorem IScalar.rMin_eq_min (ty : IScalarTy) : IScalar.rMin ty = IScalar.min ty := by
  apply (IScalar.rbound_eq_bound ty).left

theorem IScalar.rMax_eq_max (ty : IScalarTy) : IScalar.rMax ty = IScalar.max ty := by
  apply (IScalar.rbound_eq_bound ty).right

/-!
# "Conservative" Bounds

We use those because we can't compare to the isize bounds (which can't
reduce at compile-time). Whenever we perform an arithmetic operation like
addition we need to check that the result is in bounds: we first compare
to the conservative bounds, which reduces, then compare to the real bounds.

This is useful for the various #asserts that we want to reduce at
type-checking time, or when defining constants.
-/

def UScalarTy.cNumBits (ty : UScalarTy) : Nat :=
  match ty with
  | .Usize => U32.numBits
  | _ => ty.numBits

def IScalarTy.cNumBits (ty : IScalarTy) : Nat :=
  match ty with
  | .Isize => I32.numBits
  | _ => ty.numBits

theorem UScalarTy.cNumBits_le (ty : UScalarTy) : ty.cNumBits ≤ ty.numBits := by
  cases ty <;> simp only [cNumBits, U32.numBits, numBits, System.Platform.le_numBits, le_refl]

theorem IScalarTy.cNumBits_le (ty : IScalarTy) : ty.cNumBits ≤ ty.numBits := by
  cases ty <;> simp only [cNumBits, I32.numBits, numBits, System.Platform.le_numBits, le_refl]

theorem UScalarTy.cNumBits_nonzero (ty : UScalarTy) : ty.cNumBits ≠ 0 := by
  cases ty <;> simp [cNumBits, U32.numBits]

theorem IScalarTy.cNumBits_nonzero (ty : IScalarTy) : ty.cNumBits ≠ 0 := by
  cases ty <;> simp [cNumBits, I32.numBits]

def UScalar.cMax (ty : UScalarTy) : Nat :=
  match ty with
  | .Usize => UScalar.rMax .U32
  | _ => UScalar.rMax ty

def IScalar.cMin (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => IScalar.rMin .I32
  | _ => IScalar.rMin ty

def IScalar.cMax (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => IScalar.rMax .I32
  | _ => IScalar.rMax ty

@[grind ., agrind .]
theorem UScalar.hBounds {ty} (x : UScalar ty) : x.toNat < 2^ty.numBits := by
  cases ty <;> exact x.toBitVec.isLt

def UScalar.hSize {ty} (x : UScalar ty) : x.toNat < UScalar.size ty := by
  have := UScalar.hBounds x
  simp [size]
  exact this

def UScalar.rMax_eq_pow_numBits (ty : UScalarTy) : UScalar.rMax ty = 2^ty.numBits - 1 := by
  cases ty <;> simp [rMax] <;> simp_bounds

def UScalar.cMax_eq_pow_cNumBits (ty : UScalarTy) : UScalar.cMax ty = 2^ty.cNumBits - 1 := by
  cases ty <;> simp [cMax, UScalarTy.cNumBits] <;> simp_bounds

def UScalar.cMax_le_rMax (ty : UScalarTy) : UScalar.cMax ty ≤ UScalar.rMax ty := by
  have := rMax_eq_pow_numBits ty
  have := cMax_eq_pow_cNumBits ty
  have := ty.cNumBits_le
  have := @Nat.pow_le_pow_right 2 (by simp) ty.cNumBits ty.numBits ty.cNumBits_le
  omega

def UScalar.hrBounds {ty} (x : UScalar ty) : x.toNat ≤ UScalar.rMax ty := by
  have := UScalar.hBounds x
  have := UScalar.rMax_eq_pow_numBits ty
  omega

def UScalar.hmax {ty} (x : UScalar ty) : x.toNat < 2^ty.numBits := x.hBounds

theorem IScalar.hBounds {ty} (x : IScalar ty) :
  -2^(ty.numBits - 1) ≤ x.toInt ∧ x.toInt < 2^(ty.numBits - 1) := by
  have hval : x.toInt = (IScalar.toBitVec x).toInt := by
    cases ty <;> simp [toInt, toBitVec]
  rw [hval]
  have hlt : (IScalar.toBitVec x).toNat < 2^ty.numBits := (IScalar.toBitVec x).isLt
  simp only [BitVec.toInt]
  split_ifs with h
  · constructor
    · have : (0 : Int) ≤ (IScalar.toBitVec x).toNat := Int.natCast_nonneg _
      cases ty <;> simp [IScalarTy.numBits] at * <;> try omega
      all_goals (cases System.Platform.numBits_eq <;> simp_all <;> omega)
    · cases ty <;> simp [IScalarTy.numBits] at * <;> try omega
      cases System.Platform.numBits_eq <;> simp_all <;> omega
  · constructor
    · push_neg at h
      cases ty <;> simp [IScalarTy.numBits] at * <;> try omega
      cases System.Platform.numBits_eq <;> simp_all <;> omega
    · push_neg at h
      cases ty <;> simp [IScalarTy.numBits] at * <;> try omega
      cases System.Platform.numBits_eq <;> simp_all <;> omega

def IScalar.rMin_eq_pow_numBits (ty : IScalarTy) : IScalar.rMin ty = -2^(ty.numBits - 1) := by
  cases ty <;> simp_bounds

def IScalar.rMax_eq_pow_numBits (ty : IScalarTy) : IScalar.rMax ty = 2^(ty.numBits - 1) - 1 := by
  cases ty <;> simp [rMax] <;> simp_bounds

def IScalar.cMin_eq_pow_cNumBits (ty : IScalarTy) : IScalar.cMin ty = -2^(ty.cNumBits - 1) := by
  cases ty <;> simp [cMin, IScalarTy.cNumBits] <;> simp_bounds

def IScalar.cMax_eq_pow_cNumBits (ty : IScalarTy) : IScalar.cMax ty = 2^(ty.cNumBits - 1) - 1 := by
  cases ty <;> simp [cMax, IScalarTy.cNumBits] <;> simp_bounds

def IScalar.rMin_le_cMin (ty : IScalarTy) : IScalar.rMin ty ≤ IScalar.cMin ty := by
  have := rMin_eq_pow_numBits ty
  have := cMin_eq_pow_cNumBits ty
  have := ty.cNumBits_le
  have := ty.cNumBits_nonzero
  have := @Nat.pow_le_pow_right 2 (by simp) (ty.cNumBits - 1) (ty.numBits - 1) (by omega)
  zify at this
  omega

def IScalar.cMax_le_rMax (ty : IScalarTy) : IScalar.cMax ty ≤ IScalar.rMax ty := by
  have := rMax_eq_pow_numBits ty
  have := cMax_eq_pow_cNumBits ty
  have := ty.cNumBits_le
  have := ty.cNumBits_nonzero
  have := @Nat.pow_le_pow_right 2 (by simp) (ty.cNumBits - 1) (ty.numBits - 1) (by omega)
  zify at this
  omega

theorem IScalar.hrBounds {ty} (x : IScalar ty) :
  IScalar.rMin ty ≤ x.toInt ∧ x.toInt ≤ IScalar.rMax ty := by
  have := IScalar.hBounds x
  have := IScalar.rMin_eq_pow_numBits ty
  have := IScalar.rMax_eq_pow_numBits ty
  omega

def IScalar.hmin {ty} (x : IScalar ty) : -2^(ty.numBits - 1) ≤ x.toInt := x.hBounds.left
def IScalar.hmax {ty} (x : IScalar ty) : x.toInt < 2^(ty.numBits - 1) := x.hBounds.right

instance {ty} : BEq (UScalar ty) := by cases ty <;> exact inferInstance
instance {ty} : BEq (IScalar ty) := by cases ty <;> exact inferInstance

instance {ty} : LawfulBEq (UScalar ty) := by cases ty <;> exact inferInstance
instance {ty} : LawfulBEq (IScalar ty) := by cases ty <;> exact inferInstance

instance (ty : UScalarTy) : CoeOut (UScalar ty) Nat where
  coe := λ v => v.toNat

instance (ty : IScalarTy) : CoeOut (IScalar ty) Int where
  coe := λ v => v.toInt

/- Activate the ↑ notation -/
attribute [coe] UScalar.toNat IScalar.toInt

/- Concrete `CoeOut` instances for each scalar type.
   These are necessary because `U32 = abbrev UScalar .U32 = UInt32`, and Lean's
   typeclass synthesis reduces `@[reducible]` abbreviations to their WHNF before
   head-matching, so the polymorphic `CoeOut (UScalar ty) Nat` instance is not
   found when the expected type is the concrete `UInt32` / `Int32` etc.
   We explicitly use `UScalar.toNat` / `IScalar.toInt` so that the inserted
   coercion matches the existing `[coe]` and `scalar_tac` patterns. -/
instance : CoeOut UInt8   Nat where coe x := @UScalar.toNat .U8    x
instance : CoeOut UInt16  Nat where coe x := @UScalar.toNat .U16   x
instance : CoeOut UInt32  Nat where coe x := @UScalar.toNat .U32   x
instance : CoeOut UInt64  Nat where coe x := @UScalar.toNat .U64   x
instance : CoeOut UInt128 Nat where coe x := @UScalar.toNat .U128  x
instance : CoeOut USize   Nat where coe x := @UScalar.toNat .Usize x
instance : CoeOut Int8    Int where coe x := @IScalar.toInt .I8    x
instance : CoeOut Int16   Int where coe x := @IScalar.toInt .I16   x
instance : CoeOut Int32   Int where coe x := @IScalar.toInt .I32   x
instance : CoeOut Int64   Int where coe x := @IScalar.toInt .I64   x
instance : CoeOut Int128  Int where coe x := @IScalar.toInt .I128  x
instance : CoeOut ISize   Int where coe x := @IScalar.toInt .Isize x

theorem UScalar.bound_suffices (ty : UScalarTy) (x : Nat) :
  x ≤ UScalar.cMax ty -> x < 2^ty.numBits
  := by
  intro h
  have := UScalar.rMax_eq_pow_numBits ty
  have : 0 < 2^ty.numBits := by simp
  have := cMax_le_rMax ty
  omega

theorem IScalar.bound_suffices (ty : IScalarTy) (x : Int) :
  IScalar.cMin ty ≤ x ∧ x ≤ IScalar.cMax ty ->
  -2^(ty.numBits - 1) ≤ x ∧ x < 2^(ty.numBits - 1)
  := by
  intro h
  have := ty.cNumBits_nonzero
  have := ty.numBits_nonzero
  have := ty.cNumBits_le
  have := IScalar.rMin_eq_pow_numBits ty
  have := IScalar.rMax_eq_pow_numBits ty
  have := rMin_le_cMin ty
  have := cMax_le_rMax ty
  omega

def UScalar.ofNatCore {ty : UScalarTy} (x : Nat) (h : x < 2^ty.numBits) : UScalar ty :=
  UScalar.ofBitVec ty ⟨⟨x, h⟩⟩

def IScalar.ofIntCore {ty : IScalarTy} (x : Int) (_ : -2^(ty.numBits-1) ≤ x ∧ x < 2^(ty.numBits - 1)) : IScalar ty :=
  IScalar.ofBitVec ty (BitVec.ofInt ty.numBits x)

@[reducible] def UScalar.ofNat {ty : UScalarTy} (x : Nat)
  (hInBounds : x ≤ UScalar.cMax ty := by decide) : UScalar ty :=
  UScalar.ofNatCore x (UScalar.bound_suffices ty x hInBounds)

@[reducible] def IScalar.ofInt {ty : IScalarTy} (x : Int)
  (hInBounds : IScalar.cMin ty ≤ x ∧ x ≤ IScalar.cMax ty := by decide) : IScalar ty :=
  IScalar.ofIntCore x (IScalar.bound_suffices ty x hInBounds)

@[simp] abbrev UScalar.inBounds (ty : UScalarTy) (x : Nat) : Prop :=
  x < 2^ty.numBits

@[simp] abbrev IScalar.inBounds (ty : IScalarTy) (x : Int) : Prop :=
  - 2^(ty.numBits - 1) ≤ x ∧ x < 2^(ty.numBits - 1)

@[simp] abbrev UScalar.check_bounds (ty : UScalarTy) (x : Nat) : Bool :=
  x < 2^ty.numBits

@[simp] abbrev IScalar.check_bounds (ty : IScalarTy) (x : Int) : Bool :=
  -2^(ty.numBits - 1) ≤ x ∧ x < 2^(ty.numBits - 1)

theorem UScalar.check_bounds_imp_inBounds {ty : UScalarTy} {x : Nat}
  (h: UScalar.check_bounds ty x) :
  UScalar.inBounds ty x := by
  simp at *; apply h

theorem UScalar.check_bounds_eq_inBounds (ty : UScalarTy) (x : Nat) :
  UScalar.check_bounds ty x ↔ UScalar.inBounds ty x := by
  constructor <;> intro h
  . apply (check_bounds_imp_inBounds h)
  . simp_all

theorem IScalar.check_bounds_imp_inBounds {ty : IScalarTy} {x : Int}
  (h: IScalar.check_bounds ty x) :
  IScalar.inBounds ty x := by
  simp at *; apply h

theorem IScalar.check_bounds_eq_inBounds (ty : IScalarTy) (x : Int) :
  IScalar.check_bounds ty x ↔ IScalar.inBounds ty x := by
  constructor <;> intro h
  . apply (check_bounds_imp_inBounds h)
  . simp_all

def UScalar.tryMkOpt (ty : UScalarTy) (x : Nat) : Option (UScalar ty) :=
  if h:UScalar.check_bounds ty x then
    some (UScalar.ofNatCore x (UScalar.check_bounds_imp_inBounds h))
  else none

def UScalar.tryMk (ty : UScalarTy) (x : Nat) : Result (UScalar ty) :=
  Result.ofOption (tryMkOpt ty x) integerOverflow

def IScalar.tryMkOpt (ty : IScalarTy) (x : Int) : Option (IScalar ty) :=
  if h:IScalar.check_bounds ty x then
    some (IScalar.ofIntCore x (IScalar.check_bounds_imp_inBounds h))
  else none

def IScalar.tryMk (ty : IScalarTy) (x : Int) : Result (IScalar ty) :=
  Result.ofOption (tryMkOpt ty x) integerOverflow

theorem UScalar.tryMkOpt_eq (ty : UScalarTy) (x : Nat) :
  match tryMkOpt ty x with
  | some y => y.toNat = x ∧ inBounds ty x
  | none => ¬ (inBounds ty x) := by
  simp [tryMkOpt]
  have h := check_bounds_eq_inBounds ty x
  split_ifs <;> simp_all
  simp only [ofNatCore, toNat, ofBitVec]
  cases ty <;> simp [UInt128.toNat]

theorem UScalar.tryMk_eq (ty : UScalarTy) (x : Nat) :
  match tryMk ty x with
  | ok y => y.toNat = x ∧ inBounds ty x
  | fail _ => ¬ (inBounds ty x)
  | _ => False := by
  have := UScalar.tryMkOpt_eq ty x
  simp [tryMk, ofOption]
  cases h: tryMkOpt ty x <;> simp_all

theorem IScalar.tryMkOpt_eq (ty : IScalarTy) (x : Int) :
  match tryMkOpt ty x with
  | some y => y.toInt = x ∧ inBounds ty x
  | none => ¬ (inBounds ty x) := by
  simp [tryMkOpt]
  have h := check_bounds_eq_inBounds ty x
  split_ifs <;> simp_all
  simp only [ofIntCore, toInt, ofBitVec]
  cases ty <;>
    simp [Int8.toInt, Int16.toInt, Int32.toInt, Int64.toInt, Int128.toInt, ISize.toInt, Int.bmod] <;>
    split <;> (try omega) <;>
    all_goals (cases System.Platform.numBits_eq <;> simp_all <;> omega)

theorem IScalar.tryMk_eq (ty : IScalarTy) (x : Int) :
  match tryMk ty x with
  | ok y => y.toInt = x ∧ inBounds ty x
  | fail _ => ¬ (inBounds ty x)
  | _ => False := by
  have := tryMkOpt_eq ty x
  simp [tryMk]
  cases h : tryMkOpt ty x <;> simp_all

@[simp] theorem UScalar.zero_in_cbounds {ty : UScalarTy} : 0 < 2^ty.numBits := by
  simp

@[simp] theorem IScalar.zero_in_cbounds {ty : IScalarTy} :
  -2^(ty.numBits - 1) ≤ 0 ∧ 0 < 2^(ty.numBits - 1) := by
  cases ty <;> simp

/-! The scalar types. -/
abbrev  Usize := UScalar .Usize
abbrev  U8    := UScalar .U8
abbrev  U16   := UScalar .U16
abbrev  U32   := UScalar .U32
abbrev  U64   := UScalar .U64
abbrev  U128  := UScalar .U128
abbrev  Isize := IScalar .Isize
abbrev  I8    := IScalar .I8
abbrev  I16   := IScalar .I16
abbrev  I32   := IScalar .I32
abbrev  I64   := IScalar .I64
abbrev  I128  := IScalar .I128

/- Bridge lemmas: `@UScalar.toNat .X x = X.toNat x` (and likewise for signed).
   These are necessary because:
   - The coercion `(↑x : ℕ)` for `x : UIntN` inserts `@UScalar.toNat .X x`
     (as defined by the concrete `CoeOut` instances above).
   - Many simp/scalar_tac lemmas are indexed under the native `UIntN.toNat`
     head symbol (e.g. `Usize.ofNatCore_toNat_eq`, `Vec.len_val`).
   - Since `UScalar.toNat` is only `@[reducible]` (not `@[simp]`), simp will
     NOT unfold it automatically and the two forms look different to simp.
   By marking these `@[simp]`, the coercion head `@UScalar.toNat .X x` is
   normalised to `UIntN.toNat x` before simp tries other rewrites. -/
@[simp, scalar_tac_simps, grind =, agrind =]
theorem UScalar.toNat_U8_eq    (x : U8)    : @UScalar.toNat .U8    x = UInt8.toNat   x := rfl
@[simp, scalar_tac_simps, grind =, agrind =]
theorem UScalar.toNat_U16_eq   (x : U16)   : @UScalar.toNat .U16   x = UInt16.toNat  x := rfl
@[simp, scalar_tac_simps, grind =, agrind =]
theorem UScalar.toNat_U32_eq   (x : U32)   : @UScalar.toNat .U32   x = UInt32.toNat  x := rfl
@[simp, scalar_tac_simps, grind =, agrind =]
theorem UScalar.toNat_U64_eq   (x : U64)   : @UScalar.toNat .U64   x = UInt64.toNat  x := rfl
@[simp, scalar_tac_simps, grind =, agrind =]
theorem UScalar.toNat_U128_eq  (x : U128)  : @UScalar.toNat .U128  x = UInt128.toNat x := rfl
@[simp, scalar_tac_simps, grind =, agrind =]
theorem UScalar.toNat_Usize_eq (x : Usize) : @UScalar.toNat .Usize x = USize.toNat   x := rfl

@[simp, scalar_tac_simps, grind =, agrind =]
theorem IScalar.toInt_I8_eq    (x : I8)    : @IScalar.toInt .I8    x = Int8.toInt    x := rfl
@[simp, scalar_tac_simps, grind =, agrind =]
theorem IScalar.toInt_I16_eq   (x : I16)   : @IScalar.toInt .I16   x = Int16.toInt   x := rfl
@[simp, scalar_tac_simps, grind =, agrind =]
theorem IScalar.toInt_I32_eq   (x : I32)   : @IScalar.toInt .I32   x = Int32.toInt   x := rfl
@[simp, scalar_tac_simps, grind =, agrind =]
theorem IScalar.toInt_I64_eq   (x : I64)   : @IScalar.toInt .I64   x = Int64.toInt   x := rfl
@[simp, scalar_tac_simps, grind =, agrind =]
theorem IScalar.toInt_I128_eq  (x : I128)  : @IScalar.toInt .I128  x = Int128.toInt  x := rfl
@[simp, scalar_tac_simps, grind =, agrind =]
theorem IScalar.toInt_Isize_eq (x : Isize) : @IScalar.toInt .Isize x = ISize.toInt   x := rfl

/-!  ofNatCore -/
-- TODO: typeclass?
def Usize.ofNatCore := @UScalar.ofNatCore .Usize
def U8.ofNatCore    := @UScalar.ofNatCore .U8
def U16.ofNatCore   := @UScalar.ofNatCore .U16
def U32.ofNatCore   := @UScalar.ofNatCore .U32
def U64.ofNatCore   := @UScalar.ofNatCore .U64
def U128.ofNatCore  := @UScalar.ofNatCore .U128

/-!  ofIntCore -/
def Isize.ofIntCore := @IScalar.ofIntCore .Isize
def I8.ofIntCore    := @IScalar.ofIntCore .I8
def I16.ofIntCore   := @IScalar.ofIntCore .I16
def I32.ofIntCore   := @IScalar.ofIntCore .I32
def I64.ofIntCore   := @IScalar.ofIntCore .I64
def I128.ofIntCore  := @IScalar.ofIntCore .I128

/-!  ofNat -/
-- TODO: typeclass?
abbrev Usize.ofNat := @UScalar.ofNat .Usize
abbrev U8.ofNat    := @UScalar.ofNat .U8
abbrev U16.ofNat   := @UScalar.ofNat .U16
abbrev U32.ofNat   := @UScalar.ofNat .U32
abbrev U64.ofNat   := @UScalar.ofNat .U64
abbrev U128.ofNat  := @UScalar.ofNat .U128

/-!  ofInt -/
abbrev Isize.ofInt := @IScalar.ofInt .Isize
abbrev I8.ofInt    := @IScalar.ofInt .I8
abbrev I16.ofInt   := @IScalar.ofInt .I16
abbrev I32.ofInt   := @IScalar.ofInt .I32
abbrev I64.ofInt   := @IScalar.ofInt .I64
abbrev I128.ofInt  := @IScalar.ofInt .I128

@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =]
theorem UScalar.ofNatCore_toNat_eq {ty : UScalarTy} (h : x < 2^ty.numBits) :
  (UScalar.ofNatCore x h).toNat = x := by
  simp only [ofNatCore, toNat, ofBitVec]
  cases ty <;> simp [UInt128.toNat, BitVec.toNat_ofFin]

@[simp, scalar_tac_simps, grind =, agrind =]
theorem U8.ofNatCore_toNat_eq (h : x < 2^UScalarTy.U8.numBits) : (U8.ofNatCore x h).toNat = x := by
  apply UScalar.ofNatCore_toNat_eq h

@[simp, scalar_tac_simps, grind =, agrind =]
theorem U16.ofNatCore_toNat_eq (h : x < 2^UScalarTy.U16.numBits) : (U16.ofNatCore x h).toNat = x := by
  apply UScalar.ofNatCore_toNat_eq h

@[simp, scalar_tac_simps, grind =, agrind =]
theorem U32.ofNatCore_toNat_eq (h : x < 2^UScalarTy.U32.numBits) : (U32.ofNatCore x h).toNat = x := by
  apply UScalar.ofNatCore_toNat_eq h

@[simp, scalar_tac_simps, grind =, agrind =]
theorem U64.ofNatCore_toNat_eq (h : x < 2^UScalarTy.U64.numBits) : (U64.ofNatCore x h).toNat = x := by
  apply UScalar.ofNatCore_toNat_eq h

@[simp, scalar_tac_simps, grind =, agrind =]
theorem U128.ofNatCore_toNat_eq (h : x < 2^UScalarTy.U128.numBits) : (U128.ofNatCore x h).toNat = x := by
  apply UScalar.ofNatCore_toNat_eq h

@[simp, scalar_tac_simps, grind =, agrind =]
theorem Usize.ofNatCore_toNat_eq (h : x < 2^UScalarTy.Usize.numBits) : (Usize.ofNatCore x h).toNat = x := by
  apply UScalar.ofNatCore_toNat_eq h

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem UScalar.ofNat_toNat_eq {ty : UScalarTy} {x : Nat} (h : x ≤ UScalar.cMax ty) :
  (UScalar.ofNat x h).toNat = x :=
  UScalar.ofNatCore_toNat_eq _

@[simp, scalar_tac_simps, grind =, agrind =] theorem U8.ofNat_toNat_eq    {x : Nat} (h : x ≤ UScalar.cMax .U8)    : (U8.ofNat    x h).toNat = x := UScalar.ofNat_toNat_eq h
@[simp, scalar_tac_simps, grind =, agrind =] theorem U16.ofNat_toNat_eq   {x : Nat} (h : x ≤ UScalar.cMax .U16)   : (U16.ofNat   x h).toNat = x := UScalar.ofNat_toNat_eq h
@[simp, scalar_tac_simps, grind =, agrind =] theorem U32.ofNat_toNat_eq   {x : Nat} (h : x ≤ UScalar.cMax .U32)   : (U32.ofNat   x h).toNat = x := UScalar.ofNat_toNat_eq h
@[simp, scalar_tac_simps, grind =, agrind =] theorem U64.ofNat_toNat_eq   {x : Nat} (h : x ≤ UScalar.cMax .U64)   : (U64.ofNat   x h).toNat = x := UScalar.ofNat_toNat_eq h
@[simp, scalar_tac_simps, grind =, agrind =] theorem U128.ofNat_toNat_eq  {x : Nat} (h : x ≤ UScalar.cMax .U128)  : (U128.ofNat  x h).toNat = x := UScalar.ofNat_toNat_eq h
@[simp, scalar_tac_simps, grind =, agrind =] theorem Usize.ofNat_toNat_eq {x : Nat} (h : x ≤ UScalar.cMax .Usize) : (Usize.ofNat x h).toNat = x := UScalar.ofNat_toNat_eq h

/-! ### Native-type head versions of ofNat_toNat_eq

  With the `abbrev`-based scalar types, `(Usize.ofNat n h).toNat` elaborates to
  `USize.toNat (Usize.ofNat n h)` (head: `USize.toNat`) because Lean reduces
  `Usize = UScalar .Usize = USize` via WHNF before dot-notation lookup.
  The abstract `Usize.ofNat_toNat_eq` is indexed at `@UScalar.toNat` and is never
  found by simp for these goals.  We add concrete lemmas with the right head. -/
@[simp, scalar_tac_simps, grind =, agrind =] theorem UInt8.toNat_ofNat_eq   {x : Nat} (h : x ≤ UScalar.cMax .U8)    : UInt8.toNat   (U8.ofNat    x h) = x := U8.ofNat_toNat_eq h
@[simp, scalar_tac_simps, grind =, agrind =] theorem UInt16.toNat_ofNat_eq  {x : Nat} (h : x ≤ UScalar.cMax .U16)   : UInt16.toNat  (U16.ofNat   x h) = x := U16.ofNat_toNat_eq h
@[simp, scalar_tac_simps, grind =, agrind =] theorem UInt32.toNat_ofNat_eq  {x : Nat} (h : x ≤ UScalar.cMax .U32)   : UInt32.toNat  (U32.ofNat   x h) = x := U32.ofNat_toNat_eq h
@[simp, scalar_tac_simps, grind =, agrind =] theorem UInt64.toNat_ofNat_eq  {x : Nat} (h : x ≤ UScalar.cMax .U64)   : UInt64.toNat  (U64.ofNat   x h) = x := U64.ofNat_toNat_eq h
@[simp, scalar_tac_simps, grind =, agrind =] theorem UInt128.toNat_ofNat_eq {x : Nat} (h : x ≤ UScalar.cMax .U128)  : UInt128.toNat (U128.ofNat  x h) = x := U128.ofNat_toNat_eq h
@[simp, scalar_tac_simps, grind =, agrind =] theorem USize.toNat_ofNat_eq   {x : Nat} (h : x ≤ UScalar.cMax .Usize) : USize.toNat   (Usize.ofNat x h) = x := Usize.ofNat_toNat_eq h

/-- Roundtrip: `Usize.ofNat (USize.toNat x) h = x`. Needed when the result of
    `Usize.ofNat (toNat i)` must be identified with `i` by `simp`. -/
@[simp] theorem Usize.ofNat_toNat_self (x : Usize) {h : USize.toNat x ≤ UScalar.cMax .Usize} :
    Usize.ofNat (USize.toNat x) h = x :=
  USize.toNat_inj.mp (Usize.ofNat_toNat_eq h)

/-! ### Scalar equality ↔ numeric equality

  With the `abbrev`-based scalars, `x = y` for `x y : U32 = UInt32` is a `UInt32`
  equality.  `scalar_tac` needs to convert hypotheses like `¬ x = U32.ofNat 0` to
  the numeric form `x.toNat ≠ 0`.  We register the iff lemmas so simp can do this.

  IMPORTANT: the RHS uses the coercion `(x : Nat)` which elaborates to `@UScalar.toNat .U32 x`
  (via the concrete `CoeOut UInt32 Nat` instances above).  This keeps everything in the same
  syntactic form as the coercions `↑x` used by the rest of scalar_tac, so that omega can
  unify atoms across hypotheses and the goal. -/
@[simp, scalar_tac_simps] theorem U8.eq_iff_toNat_eq    (x y : U8)    : x = y ↔ (x : Nat) = (y : Nat) := UInt8.toNat_inj.symm
@[simp, scalar_tac_simps] theorem U16.eq_iff_toNat_eq   (x y : U16)   : x = y ↔ (x : Nat) = (y : Nat) := UInt16.toNat_inj.symm
@[simp, scalar_tac_simps] theorem U32.eq_iff_toNat_eq   (x y : U32)   : x = y ↔ (x : Nat) = (y : Nat) := UInt32.toNat_inj.symm
@[simp, scalar_tac_simps] theorem U64.eq_iff_toNat_eq   (x y : U64)   : x = y ↔ (x : Nat) = (y : Nat) := UInt64.toNat_inj.symm
@[simp, scalar_tac_simps] theorem U128.eq_iff_toNat_eq  (x y : U128)  : x = y ↔ (x : Nat) = (y : Nat) := UInt128.toNat_inj.symm
@[simp, scalar_tac_simps] theorem Usize.eq_iff_toNat_eq (x y : Usize) : x = y ↔ (x : Nat) = (y : Nat) := USize.toNat_inj.symm

/-! ### Signed scalar equality ↔ numeric equality (same rationale as unsigned above) -/
@[simp, scalar_tac_simps] theorem I8.eq_iff_toInt_eq    (x y : I8)    : x = y ↔ (x : Int) = (y : Int) := Int8.toInt_inj.symm
@[simp, scalar_tac_simps] theorem I16.eq_iff_toInt_eq   (x y : I16)   : x = y ↔ (x : Int) = (y : Int) := Int16.toInt_inj.symm
@[simp, scalar_tac_simps] theorem I32.eq_iff_toInt_eq   (x y : I32)   : x = y ↔ (x : Int) = (y : Int) := Int32.toInt_inj.symm
@[simp, scalar_tac_simps] theorem I64.eq_iff_toInt_eq   (x y : I64)   : x = y ↔ (x : Int) = (y : Int) := Int64.toInt_inj.symm
@[simp, scalar_tac_simps] theorem I128.eq_iff_toInt_eq  (x y : I128)  : x = y ↔ (x : Int) = (y : Int) := Int128.toInt_inj.symm
@[simp, scalar_tac_simps] theorem Isize.eq_iff_toInt_eq (x y : Isize) : x = y ↔ (x : Int) = (y : Int) := ISize.toInt_inj.symm

@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind! ., agrind! .]
theorem IScalar.ofInt_toInt_eq {ty : IScalarTy} (h : - 2^(ty.numBits - 1) ≤ x ∧ x < 2^(ty.numBits - 1)) :
  (IScalar.ofIntCore x h).toInt = x := by
  simp only [ofIntCore, toInt, ofBitVec]
  cases ty <;>
    simp [Int8.toInt, Int16.toInt, Int32.toInt, Int64.toInt, Int128.toInt, ISize.toInt, Int.bmod] <;>
    split <;> (try omega) <;>
    all_goals (cases System.Platform.numBits_eq <;> simp_all <;> omega)

@[simp, scalar_tac_simps, grind =, agrind =]
theorem I8.ofInt_toInt_eq (h : -2^(IScalarTy.I8.numBits-1) ≤ x ∧ x < 2^(IScalarTy.I8.numBits-1)) : (I8.ofIntCore x h).toInt = x := by
  apply IScalar.ofInt_toInt_eq

@[simp, scalar_tac_simps, grind =, agrind =]
theorem I16.ofInt_toInt_eq (h : -2^(IScalarTy.I16.numBits-1) ≤ x ∧ x < 2^(IScalarTy.I16.numBits-1)) : (I16.ofIntCore x h).toInt = x := by
  apply IScalar.ofInt_toInt_eq

@[simp, scalar_tac_simps, grind =, agrind =]
theorem I32.ofInt_toInt_eq (h : -2^(IScalarTy.I32.numBits-1) ≤ x ∧ x < 2^(IScalarTy.I32.numBits-1)) : (I32.ofIntCore x h).toInt = x := by
  apply IScalar.ofInt_toInt_eq

@[simp, scalar_tac_simps, grind =, agrind =]
theorem I64.ofInt_toInt_eq (h : -2^(IScalarTy.I64.numBits-1) ≤ x ∧ x < 2^(IScalarTy.I64.numBits-1)) : (I64.ofIntCore x h).toInt = x := by
  apply IScalar.ofInt_toInt_eq

@[simp, scalar_tac_simps, grind =, agrind =]
theorem I128.ofInt_toInt_eq (h : -2^(IScalarTy.I128.numBits-1) ≤ x ∧ x < 2^(IScalarTy.I128.numBits-1)) : (I128.ofIntCore x h).toInt = x := by
  apply IScalar.ofInt_toInt_eq

@[simp, scalar_tac_simps, grind =, agrind =]
theorem Isize.ofInt_toInt_eq (h : -2^(IScalarTy.Isize.numBits-1) ≤ x ∧ x < 2^(IScalarTy.Isize.numBits-1)) : (Isize.ofIntCore x h).toInt = x := by
  apply IScalar.ofInt_toInt_eq

theorem UScalar.eq_equiv_bv_eq {ty : UScalarTy} (x y : UScalar ty) :
  x = y ↔ UScalar.toBitVec x = UScalar.toBitVec y := by
  constructor
  · rintro rfl; rfl
  · intro h; cases ty <;> cases x <;> cases y <;> simp_all [UScalar.toBitVec]

@[bvify] theorem U8.eq_equiv_bv_eq (x y : U8) : x = y ↔ x.toBitVec = y.toBitVec := by apply UScalar.eq_equiv_bv_eq
@[bvify] theorem U16.eq_equiv_bv_eq (x y : U16) : x = y ↔ x.toBitVec = y.toBitVec := by apply UScalar.eq_equiv_bv_eq
@[bvify] theorem U32.eq_equiv_bv_eq (x y : U32) : x = y ↔ x.toBitVec = y.toBitVec := by apply UScalar.eq_equiv_bv_eq
@[bvify] theorem U64.eq_equiv_bv_eq (x y : U64) : x = y ↔ x.toBitVec = y.toBitVec := by apply UScalar.eq_equiv_bv_eq
@[bvify] theorem U128.eq_equiv_bv_eq (x y : U128) : x = y ↔ x.toBitVec = y.toBitVec := by apply UScalar.eq_equiv_bv_eq
@[bvify] theorem Usize.eq_equiv_bv_eq (x y : Usize) : x = y ↔ x.toBitVec = y.toBitVec := by apply UScalar.eq_equiv_bv_eq

@[ext, grind ext, agrind ext] theorem U8.bv_eq_imp_eq (x y : U8) : x.toBitVec = y.toBitVec → x = y := (UScalar.eq_equiv_bv_eq x y).mpr
@[ext, grind ext, agrind ext] theorem U16.bv_eq_imp_eq (x y : U16) : x.toBitVec = y.toBitVec → x = y := (UScalar.eq_equiv_bv_eq x y).mpr
@[ext, grind ext, agrind ext] theorem U32.bv_eq_imp_eq (x y : U32) : x.toBitVec = y.toBitVec → x = y := (UScalar.eq_equiv_bv_eq x y).mpr
@[ext, grind ext, agrind ext] theorem U64.bv_eq_imp_eq (x y : U64) : x.toBitVec = y.toBitVec → x = y := (UScalar.eq_equiv_bv_eq x y).mpr
@[ext, grind ext, agrind ext] theorem U128.bv_eq_imp_eq (x y : U128) : x.toBitVec = y.toBitVec → x = y := (UScalar.eq_equiv_bv_eq x y).mpr
@[ext, grind ext, agrind ext] theorem Usize.bv_eq_imp_eq (x y : Usize) : x.toBitVec = y.toBitVec → x = y := (UScalar.eq_equiv_bv_eq x y).mpr

theorem UScalar.ofNatCore_bv {ty : UScalarTy} (x : Nat) h :
  UScalar.toBitVec (@UScalar.ofNatCore ty x h) = BitVec.ofNat _ x := by
  rw [← BitVec.toNat_inj]
  have lhs : (UScalar.toBitVec (@UScalar.ofNatCore ty x h)).toNat = x := by cases ty <;> rfl
  simp [lhs, Nat.mod_eq_of_lt h]

@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem U8.ofNat_bv (x : Nat) h : (U8.ofNat x h).toBitVec = BitVec.ofNat _ x := by apply UScalar.ofNatCore_bv
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem U16.ofNat_bv (x : Nat) h : (U16.ofNat x h).toBitVec = BitVec.ofNat _ x := by apply UScalar.ofNatCore_bv
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem U32.ofNat_bv (x : Nat) h : (U32.ofNat x h).toBitVec = BitVec.ofNat _ x := by apply UScalar.ofNatCore_bv
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem U64.ofNat_bv (x : Nat) h : (U64.ofNat x h).toBitVec = BitVec.ofNat _ x := by apply UScalar.ofNatCore_bv
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem U128.ofNat_bv (x : Nat) h : (U128.ofNat x h).toBitVec = BitVec.ofNat _ x := by apply UScalar.ofNatCore_bv
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem Usize.ofNat_bv (x : Nat) h : (Usize.ofNat x h).toBitVec = BitVec.ofNat _ x := by apply UScalar.ofNatCore_bv

theorem IScalar.eq_equiv_bv_eq {ty : IScalarTy} (x y : IScalar ty) :
  x = y ↔ IScalar.toBitVec x = IScalar.toBitVec y := by
  cases ty <;> cases x <;> cases y <;>
    simp [IScalar.toBitVec, Int8.toBitVec, Int16.toBitVec, Int32.toBitVec,
         Int64.toBitVec, Int128.toBitVec, ISize.toBitVec,
         UInt8.toBitVec_inj, UInt16.toBitVec_inj, UInt32.toBitVec_inj,
         UInt64.toBitVec_inj, USize.toBitVec_inj, UInt128.toBitVec_inj]

@[bvify] theorem I8.eq_equiv_bv_eq (x y : I8) : x = y ↔ x.toBitVec = y.toBitVec := by apply IScalar.eq_equiv_bv_eq
@[bvify] theorem I16.eq_equiv_bv_eq (x y : I16) : x = y ↔ x.toBitVec = y.toBitVec := by apply IScalar.eq_equiv_bv_eq
@[bvify] theorem I32.eq_equiv_bv_eq (x y : I32) : x = y ↔ x.toBitVec = y.toBitVec := by apply IScalar.eq_equiv_bv_eq
@[bvify] theorem I64.eq_equiv_bv_eq (x y : I64) : x = y ↔ x.toBitVec = y.toBitVec := by apply IScalar.eq_equiv_bv_eq
@[bvify] theorem I128.eq_equiv_bv_eq (x y : I128) : x = y ↔ x.toBitVec = y.toBitVec := by apply IScalar.eq_equiv_bv_eq
@[bvify] theorem Isize.eq_equiv_bv_eq (x y : Isize) : x = y ↔ x.toBitVec = y.toBitVec := by apply IScalar.eq_equiv_bv_eq

@[ext, grind ext, agrind ext] theorem I8.bv_eq_imp_eq (x y : I8) : x.toBitVec = y.toBitVec → x = y := (IScalar.eq_equiv_bv_eq x y).mpr
@[ext, grind ext, agrind ext] theorem I16.bv_eq_imp_eq (x y : I16) : x.toBitVec = y.toBitVec → x = y := (IScalar.eq_equiv_bv_eq x y).mpr
@[ext, grind ext, agrind ext] theorem I32.bv_eq_imp_eq (x y : I32) : x.toBitVec = y.toBitVec → x = y := (IScalar.eq_equiv_bv_eq x y).mpr
@[ext, grind ext, agrind ext] theorem I64.bv_eq_imp_eq (x y : I64) : x.toBitVec = y.toBitVec → x = y := (IScalar.eq_equiv_bv_eq x y).mpr
@[ext, grind ext, agrind ext] theorem I128.bv_eq_imp_eq (x y : I128) : x.toBitVec = y.toBitVec → x = y := (IScalar.eq_equiv_bv_eq x y).mpr
@[ext, grind ext, agrind ext] theorem Isize.bv_eq_imp_eq (x y : Isize) : x.toBitVec = y.toBitVec → x = y := (IScalar.eq_equiv_bv_eq x y).mpr

theorem IScalar.ofIntCore_bv {ty : IScalarTy} (x : Int) h :
  IScalar.toBitVec (@IScalar.ofIntCore ty x h) = BitVec.ofInt _ x := by
  simp only [ofIntCore, IScalar.toBitVec, ofBitVec]
  cases ty <;> simp

@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem I8.ofInt_bv (x : Int) h : (I8.ofInt x h).toBitVec = BitVec.ofInt _ x := by apply IScalar.ofIntCore_bv
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem I16.ofInt_bv (x : Int) h : (I16.ofInt x h).toBitVec = BitVec.ofInt _ x := by apply IScalar.ofIntCore_bv
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem I32.ofInt_bv (x : Int) h : (I32.ofInt x h).toBitVec = BitVec.ofInt _ x := by apply IScalar.ofIntCore_bv
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem I64.ofInt_bv (x : Int) h : (I64.ofInt x h).toBitVec = BitVec.ofInt _ x := by apply IScalar.ofIntCore_bv
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem I128.ofInt_bv (x : Int) h : (I128.ofInt x h).toBitVec = BitVec.ofInt _ x := by apply IScalar.ofIntCore_bv
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =] theorem Isize.ofInt_bv (x : Int) h : (Isize.ofInt x h).toBitVec = BitVec.ofInt _ x := by apply IScalar.ofIntCore_bv

instance (ty : UScalarTy) : Inhabited (UScalar ty) := by
  constructor; cases ty <;> apply (UScalar.ofNat 0 (by simp))

instance (ty : IScalarTy) : Inhabited (IScalar ty) := by
  constructor; cases ty <;> apply (IScalar.ofInt 0 (by simp [IScalar.cMin, IScalar.cMax, IScalar.rMin, IScalar.rMax]; simp_bounds))

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem UScalar.default_toNat {ty} : (default : UScalar ty).toNat = 0 := by
  cases ty <;> rfl

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem UScalar.default_bv {ty} : UScalar.toBitVec (default : UScalar ty) = 0 := by
  cases ty <;> rfl

theorem IScalar.min_lt_max (ty : IScalarTy) : IScalar.min ty < IScalar.max ty := by
  cases ty <;> simp [IScalar.min, IScalar.max, IScalarTy.numBits] <;> (try simp_bounds)
  have : (0 : Int) < 2 ^ (System.Platform.numBits - 1) := by simp
  omega

theorem IScalar.min_le_max (ty : IScalarTy) : IScalar.min ty ≤ IScalar.max ty := by
  have := IScalar.min_lt_max ty
  scalar_tac

@[reducible] def core.num.U8.MIN : U8 := UScalar.ofNat 0
@[reducible] def core.num.U8.MAX : U8 := UScalar.ofNat U8.rMax
@[reducible] def core.num.U16.MIN : U16 := UScalar.ofNat 0
@[reducible] def core.num.U16.MAX : U16 := UScalar.ofNat U16.rMax
@[reducible] def core.num.U32.MIN : U32 := UScalar.ofNat 0
@[reducible] def core.num.U32.MAX : U32 := UScalar.ofNat U32.rMax
@[reducible] def core.num.U64.MIN : U64 := UScalar.ofNat 0
@[reducible] def core.num.U64.MAX : U64 := UScalar.ofNat U64.rMax
@[reducible] def core.num.U128.MIN : U128 := UScalar.ofNat 0
@[reducible] def core.num.U128.MAX : U128 := UScalar.ofNat U128.rMax
@[reducible] def core.num.Usize.MIN : Usize := UScalar.ofNatCore 0 (by simp)
@[reducible] def core.num.Usize.MAX : Usize := UScalar.ofNatCore Usize.max (by simp [Usize.max, Usize.numBits])

@[reducible] def core.num.I8.MIN : I8 := IScalar.ofInt I8.rMin
@[reducible] def core.num.I8.MAX : I8 := IScalar.ofInt I8.rMax
@[reducible] def core.num.I16.MIN : I16 := IScalar.ofInt I16.rMin
@[reducible] def core.num.I16.MAX : I16 := IScalar.ofInt I16.rMax
@[reducible] def core.num.I32.MIN : I32 := IScalar.ofInt I32.rMin
@[reducible] def core.num.I32.MAX : I32 := IScalar.ofInt I32.rMax
@[reducible] def core.num.I64.MIN : I64 := IScalar.ofInt I64.rMin
@[reducible] def core.num.I64.MAX : I64 := IScalar.ofInt I64.rMax
@[reducible] def core.num.I128.MIN : I128 := IScalar.ofInt I128.rMin
@[reducible] def core.num.I128.MAX : I128 := IScalar.ofInt I128.rMax
@[reducible] def core.num.Isize.MIN : Isize := IScalar.ofIntCore Isize.min (by simp [Isize.min, Isize.numBits])
@[reducible] def core.num.Isize.MAX : Isize := IScalar.ofIntCore Isize.max (by simp [Isize.max, Isize.numBits, IScalarTy.numBits]; (have : (0 : Int) < 2 ^ (System.Platform.numBits - 1) := by simp); omega)


/-! # Comparisons -/
instance {ty} : LT (UScalar ty) := by cases ty <;> infer_instance

instance {ty} : LE (UScalar ty) := by cases ty <;> infer_instance

instance {ty} : LT (IScalar ty) := by cases ty <;> infer_instance

instance {ty} : LE (IScalar ty) := by cases ty <;> infer_instance

/- Not marking this one with @[simp] on purpose: if we have `x = y` somewhere in the context,
   we may want to use it to substitute `y` with `x` somewhere. -/
@[scalar_tac_simps] theorem UScalar.eq_equiv {ty : UScalarTy} (x y : UScalar ty) :
  x = y ↔ (↑x : Nat) = ↑y := by
  cases ty <;> cases x <;> cases y <;> simp_all [toNat, toBitVec, BitVec.toNat_eq]

@[ext, grind ext, agrind ext] theorem UScalar.toNat_eq_imp {ty : UScalarTy} (x y : UScalar ty) :
  (↑x : Nat) = ↑y → x = y := by
  simp [eq_equiv]

theorem UScalar.eq_imp {ty : UScalarTy} (x y : UScalar ty) :
  (↑x : Nat) = ↑y → x = y := (eq_equiv x y).mpr

@[simp, scalar_tac_simps, grind =, agrind =] theorem UScalar.lt_equiv {ty : UScalarTy} (x y : UScalar ty) :
  x < y ↔ (↑x : Nat) < ↑y := by cases ty <;> rfl

@[simp] theorem UScalar.lt_imp {ty : UScalarTy} (x y : UScalar ty) :
  (↑x : Nat) < (↑y) → x < y := (lt_equiv x y).mpr

@[simp, scalar_tac_simps, grind =, agrind =] theorem UScalar.le_equiv {ty : UScalarTy} (x y : UScalar ty) :
  x ≤ y ↔ (↑x : Nat) ≤ ↑y := by cases ty <;> rfl

@[simp] theorem UScalar.le_imp {ty : UScalarTy} (x y : UScalar ty) :
  (↑x : Nat) ≤ ↑y → x ≤ y := (le_equiv x y).mpr

@[scalar_tac_simps] theorem IScalar.eq_equiv {ty : IScalarTy} (x y : IScalar ty) :
  x = y ↔ (↑x : Int) = ↑y := by
  rw [IScalar.eq_equiv_bv_eq]
  cases ty <;> cases x <;> cases y <;>
    simp only [IScalar.toBitVec, IScalar.toInt,
               Int8.toBitVec, Int8.toInt, Int16.toBitVec, Int16.toInt,
               Int32.toBitVec, Int32.toInt, Int64.toBitVec, Int64.toInt,
               Int128.toBitVec, Int128.toInt, ISize.toBitVec, ISize.toInt] <;>
    exact BitVec.toInt_inj.symm

@[ext, grind ext, agrind ext] theorem IScalar.toInt_eq_imp {ty : IScalarTy} (x y : IScalar ty) :
  (↑x : Int) = ↑y → x = y := by
  simp [eq_equiv]

theorem IScalar.eq_imp {ty : IScalarTy} (x y : IScalar ty) :
  (↑x : Int) = ↑y → x = y := (eq_equiv x y).mpr

@[simp, scalar_tac_simps, grind =, agrind =] theorem IScalar.lt_equiv {ty : IScalarTy} (x y : IScalar ty) :
  x < y ↔ (↑x : Int) < ↑y := by cases ty <;> apply x.lt_iff_toInt_lt

@[simp, scalar_tac_simps] theorem IScalar.lt_imp {ty : IScalarTy} (x y : IScalar ty) :
  (↑x : Int) < (↑y) → x < y := (lt_equiv x y).mpr

@[simp, scalar_tac_simps, grind =, agrind =] theorem IScalar.le_equiv {ty : IScalarTy} (x y : IScalar ty) :
  x ≤ y ↔ (↑x : Int) ≤ ↑y := by cases ty <;> apply x.le_iff_toInt_le

@[simp] theorem IScalar.le_imp {ty : IScalarTy} (x y : IScalar ty) :
  (↑x : Int) ≤ ↑y → x ≤ y := (le_equiv x y).mpr

instance UScalar.decLt {ty} (a b : UScalar ty) : Decidable (LT.lt a b) := by cases ty <;> infer_instance
instance UScalar.decLe {ty} (a b : UScalar ty) : Decidable (LE.le a b) := by cases ty <;> infer_instance
instance IScalar.decLt {ty} (a b : IScalar ty) : Decidable (LT.lt a b) := by cases ty <;> infer_instance
instance IScalar.decLe {ty} (a b : IScalar ty) : Decidable (LE.le a b) := by cases ty <;> infer_instance

theorem UScalar.eq_of_toNat_eq {ty} : ∀ {i j : UScalar ty}, Eq i.toNat j.toNat → Eq i j := by
  intro i j hEq
  exact (UScalar.eq_equiv i j).mpr hEq

theorem IScalar.eq_of_toInt_eq {ty} : ∀ {i j : IScalar ty}, Eq i.toInt j.toInt → Eq i j := by
  intro i j hEq
  exact (IScalar.eq_equiv i j).mpr hEq

theorem UScalar.toNat_eq_of_eq {ty} {i j : UScalar ty} (h : Eq i j) : Eq i.toNat j.toNat := h ▸ rfl
theorem IScalar.toInt_eq_of_eq {ty} {i j : IScalar ty} (h : Eq i j) : Eq i.toInt j.toInt := h ▸ rfl

theorem UScalar.ne_of_toNat_ne {ty} {i j : UScalar ty} (h : Not (Eq i.toNat j.toNat)) : Not (Eq i j) :=
  fun h' => absurd (toNat_eq_of_eq h') h

theorem IScalar.ne_of_toInt_ne {ty} {i j : IScalar ty} (h : Not (Eq i.toInt j.toInt)) : Not (Eq i j) :=
  fun h' => absurd (toInt_eq_of_eq h') h

instance (ty : UScalarTy) : DecidableEq (UScalar ty) :=
  fun i j =>
    match decEq i.toNat j.toNat with
    | isTrue h  => isTrue (UScalar.eq_of_toNat_eq h)
    | isFalse h => isFalse (UScalar.ne_of_toNat_ne h)

instance (ty : IScalarTy) : DecidableEq (IScalar ty) :=
  fun i j =>
    match decEq i.toInt j.toInt with
    | isTrue h  => isTrue (IScalar.eq_of_toInt_eq h)
    | isFalse h => isFalse (IScalar.ne_of_toInt_ne h)

@[simp, scalar_tac_simps]
theorem UScalar.neq_to_neq_val {ty} :
  ∀ {i j : UScalar ty}, (¬ i = j) ↔ ¬ i.toNat = j.toNat := by
  simp [eq_equiv]

@[simp, scalar_tac_simps]
theorem IScalar.neq_to_neq_val {ty} :
  ∀ {i j : IScalar ty}, (¬ i = j) ↔ ¬ i.toInt = j.toInt := by
  simp [eq_equiv]

@[simp]
theorem UScalar.toNat_not_eq_imp_not_eq (x y : UScalar ty) (h : Nat.not_eq x.toNat y.toNat) :
  ¬ x = y := by
  simp_all; scalar_tac

@[simp]
theorem IScalar.toInt_not_eq_imp_not_eq (x y : IScalar ty) (h : Int.not_eq x.toInt y.toInt) :
  ¬ x = y := by
  simp_all; scalar_tac

instance (ty: UScalarTy) : Preorder (UScalar ty) where
  le_refl := fun a => by simp
  le_trans := fun a b c => by grind
  lt_iff_le_not_ge := fun a b => by grind

instance (ty: IScalarTy) : Preorder (IScalar ty) where
  le_refl := fun a => by simp
  le_trans := fun a b c => by grind
  lt_iff_le_not_ge := fun a b => by grind

instance (ty: UScalarTy) : PartialOrder (UScalar ty) where
  le_antisymm := fun a b Hab Hba =>
    UScalar.eq_imp _ _ ((@le_antisymm Nat _ _ _ ((UScalar.le_equiv a b).1 Hab) ((UScalar.le_equiv b a).1 Hba)))

instance (ty: IScalarTy) : PartialOrder (IScalar ty) where
  le_antisymm := fun a b Hab Hba =>
    IScalar.eq_imp _ _ ((@le_antisymm Int _ _ _ ((IScalar.le_equiv a b).1 Hab) ((IScalar.le_equiv b a).1 Hba)))

instance (ty : UScalarTy) : LinearOrder (UScalar ty) where
  le_total := fun a b => by
    rcases Nat.le_total (a : Nat) (b : Nat) with h | h
    · exact Or.inl ((UScalar.le_equiv a b).mpr h)
    · exact Or.inr ((UScalar.le_equiv b a).mpr h)
  toDecidableLE := fun a b => inferInstance

instance (ty : IScalarTy) : LinearOrder (IScalar ty) where
  le_total := fun a b => by
    rcases le_total (a : Int) (b : Int) with h | h
    · exact Or.inl ((IScalar.le_equiv a b).mpr h)
    · exact Or.inr ((IScalar.le_equiv b a).mpr h)
  toDecidableLE := fun a b => inferInstance

/-! # SizeOf -/

noncomputable instance (ty : IScalarTy) : SizeOf (IScalar ty) := by cases ty <;> infer_instance

noncomputable instance (ty : UScalarTy) : SizeOf (UScalar ty) := by cases ty <;> infer_instance

/-! # Coercion Theorems

    This is helpful whenever you want to "push" casts to the innermost nodes
    and make the cast normalization happen more magically. -/

@[simp, norm_cast, scalar_tac_simps, grind =, agrind =]
theorem UScalar.coe_max {ty: UScalarTy} (a b: UScalar ty): ↑(Max.max a b) = (Max.max (↑a) (↑b): ℕ) := by
  rw[_root_.max_def, _root_.max_def]
  split_ifs <;> simp_all

@[simp, norm_cast, scalar_tac_simps, grind =, agrind =]
theorem IScalar.coe_max {ty: IScalarTy} (a b: IScalar ty): ↑(Max.max a b) = (Max.max (↑a) (↑b): ℤ) := by
  rw[_root_.max_def, _root_.max_def]
  split_ifs <;> simp_all

@[simp, norm_cast, scalar_tac_simps, grind =, agrind =]
theorem UScalar.coe_min {ty: UScalarTy} (a b: UScalar ty): ↑(Min.min a b) = (Min.min (↑a) (↑b): ℕ) := by
  rw[_root_.min_def, _root_.min_def]
  split_ifs <;> simp_all

@[simp, norm_cast, scalar_tac_simps, grind =, agrind =]
theorem IScalar.coe_min {ty: IScalarTy} (a b: IScalar ty): ↑(Min.min a b) = (Min.min (↑a) (↑b): ℤ) := by
  rw[_root_.min_def, _root_.min_def]
  split_ifs <;> simp_all

/-! Max/Min theory -/

theorem UScalar.zero_le {ty} (x: UScalar ty): UScalar.ofNat 0 (by simp) ≤ x := by simp

@[simp]
theorem UScalar.max_left_zero_eq {ty} (x: UScalar ty):
  Max.max (UScalar.ofNat 0 (by simp)) x = x := max_eq_right (UScalar.zero_le x)

@[simp]
theorem UScalar.max_right_zero_eq {ty} (x: UScalar ty):
  Max.max x (UScalar.ofNat 0 (by simp)) = x := max_eq_left (UScalar.zero_le x)

/-! Some conversions -/
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind, agrind] abbrev IScalar.toNat {ty} (x : IScalar ty) : Nat := x.toInt.toNat
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind, agrind] abbrev I8.toNat      (x : I8) : Nat := x.toInt.toNat
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind, agrind] abbrev I16.toNat     (x : I16) : Nat := x.toInt.toNat
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind, agrind] abbrev I32.toNat     (x : I32) : Nat := x.toInt.toNat
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind, agrind] abbrev I64.toNat     (x : I64) : Nat := x.toInt.toNat
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind, agrind] abbrev I128.toNat    (x : I128) : Nat := x.toInt.toNat
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind, agrind] abbrev Isize.toNat   (x : Isize) : Nat := x.toInt.toNat

abbrev U8.bv (x : U8)   : BitVec 8 := UScalar.toBitVec x
abbrev U16.bv (x : U16) : BitVec 16 := UScalar.toBitVec x
abbrev U32.bv (x : U32) : BitVec 32 := UScalar.toBitVec x
abbrev U64.bv (x : U64) : BitVec 64 := UScalar.toBitVec x
abbrev U128.bv (x : U128) : BitVec 128 := UScalar.toBitVec x
abbrev Usize.bv (x : Usize) : BitVec System.Platform.numBits := UScalar.toBitVec x

abbrev I8.bv (x : I8) : BitVec 8 := IScalar.toBitVec x
abbrev I16.bv (x : I16) : BitVec 16 := IScalar.toBitVec x
abbrev I32.bv (x : I32) : BitVec 32 := IScalar.toBitVec x
abbrev I64.bv (x : I64) : BitVec 64 := IScalar.toBitVec x
abbrev I128.bv (x : I128) : BitVec 128 := IScalar.toBitVec x
abbrev Isize.bv (x : Isize) : BitVec System.Platform.numBits := IScalar.toBitVec x

/- Concrete-type `.toBitVec` dot-notation aliases.  These ensure that `x.toBitVec` for a
   concrete scalar type (e.g. `x : U32`) resolves to `U32.toBitVec x : BitVec 32` rather
   than the polymorphic `UScalar.toBitVec x : BitVec UScalarTy.U32.numBits`.  The concrete
   return type is needed for type-class synthesis (which works at reducible transparency). -/
abbrev U8.toBitVec   (x : U8)    : BitVec 8                    := UScalar.toBitVec x
abbrev U16.toBitVec  (x : U16)   : BitVec 16                   := UScalar.toBitVec x
abbrev U32.toBitVec  (x : U32)   : BitVec 32                   := UScalar.toBitVec x
abbrev U64.toBitVec  (x : U64)   : BitVec 64                   := UScalar.toBitVec x
abbrev U128.toBitVec (x : U128)  : BitVec 128                  := UScalar.toBitVec x
abbrev Usize.toBitVec (x : Usize) : BitVec System.Platform.numBits := UScalar.toBitVec x

abbrev I8.toBitVec   (x : I8)    : BitVec 8                    := IScalar.toBitVec x
abbrev I16.toBitVec  (x : I16)   : BitVec 16                   := IScalar.toBitVec x
abbrev I32.toBitVec  (x : I32)   : BitVec 32                   := IScalar.toBitVec x
abbrev I64.toBitVec  (x : I64)   : BitVec 64                   := IScalar.toBitVec x
abbrev I128.toBitVec (x : I128)  : BitVec 128                  := IScalar.toBitVec x
abbrev Isize.toBitVec (x : Isize) : BitVec System.Platform.numBits := IScalar.toBitVec x

@[simp, scalar_tac_simps, grind =, agrind =] theorem UScalar.toBitVec_toNat {ty : UScalarTy} (x : UScalar ty) :
  (UScalar.toBitVec x).toNat = x.toNat := by
  cases ty <;> simp [toBitVec, toNat, UInt128.toNat]

@[simp, scalar_tac_simps, grind =, agrind =] theorem U8.toBitVec_toNat (x : U8) : x.toBitVec.toNat = x.toNat := by apply UScalar.toBitVec_toNat
@[simp, scalar_tac_simps, grind =, agrind =] theorem U16.toBitVec_toNat (x : U16) : x.toBitVec.toNat = x.toNat := by apply UScalar.toBitVec_toNat
@[simp, scalar_tac_simps, grind =, agrind =] theorem U32.toBitVec_toNat (x : U32) : x.toBitVec.toNat = x.toNat := by apply UScalar.toBitVec_toNat
@[simp, scalar_tac_simps, grind =, agrind =] theorem U64.toBitVec_toNat (x : U64) : x.toBitVec.toNat = x.toNat := by apply UScalar.toBitVec_toNat
@[simp, scalar_tac_simps, grind =, agrind =] theorem U128.toBitVec_toNat (x : U128) : x.toBitVec.toNat = x.toNat := by apply UScalar.toBitVec_toNat
@[simp, scalar_tac_simps, grind =, agrind =] theorem Usize.toBitVec_toNat (x : Usize) : x.toBitVec.toNat = x.toNat := by apply UScalar.toBitVec_toNat

@[simp, scalar_tac_simps, grind =, agrind =] theorem IScalar.toBitVec_toInt {ty : IScalarTy} (x : IScalar ty) :
  (IScalar.toBitVec x).toInt = x.toInt := by
  cases ty <;> rfl

/-! ## `ofBitVec` round-trip lemmas -/

/-- Round-trip: constructing a scalar from a `BitVec` and extracting the `BitVec` back gives the original. -/
@[simp, bvify] theorem UScalar.ofBitVec_toBitVec (ty : UScalarTy) (bv : BitVec ty.numBits) :
  UScalar.toBitVec (UScalar.ofBitVec ty bv) = bv := by
  cases ty <;> rfl

/-- The natural number of a scalar constructed from a `BitVec` equals that `BitVec`'s `toNat`. -/
@[simp] theorem UScalar.ofBitVec_toNat (ty : UScalarTy) (bv : BitVec ty.numBits) :
  (UScalar.ofBitVec ty bv).toNat = bv.toNat := by
  rw [← toBitVec_toNat, ofBitVec_toBitVec]

/-- Round-trip: constructing a signed scalar from a `BitVec` and extracting the `BitVec` back gives the original. -/
@[simp, bvify] theorem IScalar.ofBitVec_toBitVec (ty : IScalarTy) (bv : BitVec ty.numBits) :
  IScalar.toBitVec (IScalar.ofBitVec ty bv) = bv := by
  cases ty <;> rfl

/-- The integer of a signed scalar constructed from a `BitVec` equals that `BitVec`'s `toInt`. -/
@[simp] theorem IScalar.ofBitVec_toInt (ty : IScalarTy) (bv : BitVec ty.numBits) :
  (IScalar.ofBitVec ty bv).toInt = bv.toInt := by
  cases ty <;> rfl

@[simp, scalar_tac_simps, grind =, agrind =] theorem I8.toBitVec_toInt (x : I8) : x.toBitVec.toInt = x.toInt := by apply IScalar.toBitVec_toInt
@[simp, scalar_tac_simps, grind =, agrind =] theorem I16.toBitVec_toInt (x : I16) : x.toBitVec.toInt = x.toInt := by apply IScalar.toBitVec_toInt
@[simp, scalar_tac_simps, grind =, agrind =] theorem I32.toBitVec_toInt (x : I32) : x.toBitVec.toInt = x.toInt := by apply IScalar.toBitVec_toInt
@[simp, scalar_tac_simps, grind =, agrind =] theorem I64.toBitVec_toInt (x : I64) : x.toBitVec.toInt = x.toInt := by apply IScalar.toBitVec_toInt
@[simp, scalar_tac_simps, grind =, agrind =] theorem I128.toBitVec_toInt (x : I128) : x.toBitVec.toInt = x.toInt := by apply IScalar.toBitVec_toInt
@[simp, scalar_tac_simps, grind =, agrind =] theorem Isize.toBitVec_toInt (x : Isize) : x.toBitVec.toInt = x.toInt := by apply IScalar.toBitVec_toInt

@[bvify] theorem U8.lt_succ_max (x: U8) : x.toNat < 256 := by have := x.hBounds; simp [UScalarTy.numBits] at this; omega
@[bvify] theorem U16.lt_succ_max (x: U16) : x.toNat < 65536 := by have := x.hBounds; simp [UScalarTy.numBits] at this; omega
@[bvify] theorem U32.lt_succ_max (x: U32) : x.toNat < 4294967296 := by have := x.hBounds; simp [UScalarTy.numBits] at this; omega
@[bvify] theorem U64.lt_succ_max (x: U64) : x.toNat < 18446744073709551616 := by have := x.hBounds; simp [UScalarTy.numBits] at this; omega
@[bvify] theorem U128.lt_succ_max (x: U128) : x.toNat < 340282366920938463463374607431768211456 := by have := x.hBounds; simp [UScalarTy.numBits] at this; omega

@[bvify] theorem U8.le_max (x: U8) : x.toNat ≤ 255 := by have := x.hBounds; simp [UScalarTy.numBits] at this; omega
@[bvify] theorem U16.le_max (x: U16) : x.toNat ≤ 65535 := by have := x.hBounds; simp [UScalarTy.numBits] at this; omega
@[bvify] theorem U32.le_max (x: U32) : x.toNat ≤ 4294967295 := by have := x.hBounds; simp [UScalarTy.numBits] at this; omega
@[bvify] theorem U64.le_max (x: U64) : x.toNat ≤ 18446744073709551615 := by have := x.hBounds; simp [UScalarTy.numBits] at this; omega
@[bvify] theorem U128.le_max (x: U128) : x.toNat ≤ 340282366920938463463374607431768211455 := by have := x.hBounds; simp [UScalarTy.numBits] at this; omega

@[simp, scalar_tac_simps, grind =, agrind =]
theorem UScalar.ofNat_self_toNat (x : UScalar ty) (hInBounds : x.toNat ≤ UScalar.cMax ty) :
  UScalar.ofNat x hInBounds = x := by scalar_tac

@[simp, scalar_tac_simps, grind =, agrind =]
theorem IScalar.ofInt_self_toInt (x : IScalar ty) (hInBounds : IScalar.cMin ty ≤ x.toInt ∧ x.toInt ≤ IScalar.cMax ty) :
  IScalar.ofInt x hInBounds = x := by scalar_tac

@[simp, bvify] theorem UScalar.BitVec_ofNat_toNat (x : UScalar ty) : BitVec.ofNat ty.numBits x.toNat = UScalar.toBitVec x := by
  cases ty <;> simp [toNat, toBitVec, UInt128.toNat, BitVec.ofNat_toNat]

@[simp, bvify] theorem U8.BitVec_ofNat_toNat (x : U8) : BitVec.ofNat 8 x.toNat = x.toBitVec := by apply UScalar.BitVec_ofNat_toNat
@[simp, bvify] theorem U16.BitVec_ofNat_toNat (x : U16) : BitVec.ofNat 16 x.toNat = x.toBitVec := by apply UScalar.BitVec_ofNat_toNat
@[simp, bvify] theorem U32.BitVec_ofNat_toNat (x : U32) : BitVec.ofNat 32 x.toNat = x.toBitVec := by apply UScalar.BitVec_ofNat_toNat
@[simp, bvify] theorem U64.BitVec_ofNat_toNat (x : U64) : BitVec.ofNat 64 x.toNat = x.toBitVec := by apply UScalar.BitVec_ofNat_toNat
@[simp, bvify] theorem U128.BitVec_ofNat_toNat (x : U128) : BitVec.ofNat 128 x.toNat = x.toBitVec := by apply UScalar.BitVec_ofNat_toNat
@[simp, bvify] theorem Usize.BitVec_ofNat_toNat (x : Usize) : BitVec.ofNat System.Platform.numBits x.toNat = x.toBitVec := by apply UScalar.BitVec_ofNat_toNat

/- The following lemmas rewrite `BitVec.ofNat n (native_toNat x)` to `x.toBitVec`, where
   `native_toNat` is the concrete `UIntN.toNat` function (as opposed to `UScalar.toNat`).
   These are needed because the Lean coercion `(↑x : ℕ)` when `x : UIntN` reduces to
   `UIntN.toNat x` (not `UScalar.toNat x`), and `simp` does not look through `@[reducible]`
   definitions. -/
@[simp, bvify] theorem U8.BitVec_ofNat_native_toNat (x : U8) : BitVec.ofNat 8 (UInt8.toNat x) = x.toBitVec :=
  U8.BitVec_ofNat_toNat x
@[simp, bvify] theorem U16.BitVec_ofNat_native_toNat (x : U16) : BitVec.ofNat 16 (UInt16.toNat x) = x.toBitVec :=
  U16.BitVec_ofNat_toNat x
@[simp, bvify] theorem U32.BitVec_ofNat_native_toNat (x : U32) : BitVec.ofNat 32 (UInt32.toNat x) = x.toBitVec :=
  U32.BitVec_ofNat_toNat x
@[simp, bvify] theorem U64.BitVec_ofNat_native_toNat (x : U64) : BitVec.ofNat 64 (UInt64.toNat x) = x.toBitVec :=
  U64.BitVec_ofNat_toNat x
@[simp, bvify] theorem Usize.BitVec_ofNat_native_toNat (x : Usize) : BitVec.ofNat System.Platform.numBits (USize.toNat x) = x.toBitVec :=
  Usize.BitVec_ofNat_toNat x

@[simp, bvify]
theorem IScalar.BitVec_ofInt_toInt (x : IScalar ty) : BitVec.ofInt ty.numBits x.toInt = IScalar.toBitVec x := by
  rw [← IScalar.toBitVec_toInt]; exact BitVec.ofInt_toInt

@[simp, bvify] theorem I8.BitVec_ofInt_toInt (x : I8) : BitVec.ofInt 8 x.toInt = x.toBitVec := IScalar.BitVec_ofInt_toInt x
@[simp, bvify] theorem I16.BitVec_ofInt_toInt (x : I16) : BitVec.ofInt 16 x.toInt = x.toBitVec := IScalar.BitVec_ofInt_toInt x
@[simp, bvify] theorem I32.BitVec_ofInt_toInt (x : I32) : BitVec.ofInt 32 x.toInt = x.toBitVec := IScalar.BitVec_ofInt_toInt x
@[simp, bvify] theorem I64.BitVec_ofInt_toInt (x : I64) : BitVec.ofInt 64 x.toInt = x.toBitVec := IScalar.BitVec_ofInt_toInt x
@[simp, bvify] theorem I128.BitVec_ofInt_toInt (x : I128) : BitVec.ofInt 128 x.toInt = x.toBitVec := IScalar.BitVec_ofInt_toInt x
@[simp, bvify] theorem Isize.BitVec_ofInt_toInt (x : Isize) : BitVec.ofInt System.Platform.numBits x.toInt = x.toBitVec := IScalar.BitVec_ofInt_toInt x

@[simp, bvify]
theorem UScalar.Nat_cast_BitVec_toNat (x : UScalar ty) : Nat.cast x.toNat = UScalar.toBitVec x := by
  simp only [BitVec.natCast_eq_ofNat, UScalar.BitVec_ofNat_toNat]

@[simp, bvify] theorem U8.Nat_cast_BitVec_toNat (x : U8) : Nat.cast x.toNat = x.toBitVec := UScalar.Nat_cast_BitVec_toNat x
@[simp, bvify] theorem U16.Nat_cast_BitVec_toNat (x : U16) : Nat.cast x.toNat = x.toBitVec := UScalar.Nat_cast_BitVec_toNat x
@[simp, bvify] theorem U32.Nat_cast_BitVec_toNat (x : U32) : Nat.cast x.toNat = x.toBitVec := UScalar.Nat_cast_BitVec_toNat x
@[simp, bvify] theorem U64.Nat_cast_BitVec_toNat (x : U64) : Nat.cast x.toNat = x.toBitVec := UScalar.Nat_cast_BitVec_toNat x
@[simp, bvify] theorem U128.Nat_cast_BitVec_toNat (x : U128) : Nat.cast x.toNat = x.toBitVec := UScalar.Nat_cast_BitVec_toNat x
@[simp, bvify] theorem Usize.Nat_cast_BitVec_toNat (x : Usize) : Nat.cast x.toNat = x.toBitVec := UScalar.Nat_cast_BitVec_toNat x

@[simp, bvify]
theorem IScalar.Nat_cast_BitVec_toInt (x : IScalar ty) : Int.cast x.toInt = IScalar.toBitVec x := by
  simp only [Int.cast, IntCast.intCast, BitVec_ofInt_toInt]

@[simp, bvify] theorem I8.Nat_cast_BitVec_toInt (x : I8) : Int.cast x.toInt = x.toBitVec := IScalar.Nat_cast_BitVec_toInt x
@[simp, bvify] theorem I16.Nat_cast_BitVec_toInt (x : I16) : Int.cast x.toInt = x.toBitVec := IScalar.Nat_cast_BitVec_toInt x
@[simp, bvify] theorem I32.Nat_cast_BitVec_toInt (x : I32) : Int.cast x.toInt = x.toBitVec := IScalar.Nat_cast_BitVec_toInt x
@[simp, bvify] theorem I64.Nat_cast_BitVec_toInt (x : I64) : Int.cast x.toInt = x.toBitVec := IScalar.Nat_cast_BitVec_toInt x
@[simp, bvify] theorem I128.Nat_cast_BitVec_toInt (x : I128) : Int.cast x.toInt = x.toBitVec := IScalar.Nat_cast_BitVec_toInt x
@[simp, bvify] theorem Isize.Nat_cast_BitVec_toInt (x : Isize) : Int.cast x.toInt = x.toBitVec := IScalar.Nat_cast_BitVec_toInt x

/-!
Adding theorems to the `zify_simps` simplification set.
-/
attribute [zify_simps] UScalar.eq_equiv IScalar.eq_equiv
                       UScalar.lt_equiv IScalar.lt_equiv
                       UScalar.le_equiv IScalar.le_equiv

attribute [zify_simps] U8.toBitVec_toNat U16.toBitVec_toNat U32.toBitVec_toNat
                       U64.toBitVec_toNat U128.toBitVec_toNat Usize.toBitVec_toNat

@[simp, step_post_simps] theorem UScalar.size_UScalarTyU8 : UScalar.size .U8 = U8.size := by simp_bounds
@[simp, step_post_simps] theorem UScalar.size_UScalarTyU16 : UScalar.size .U16 = U16.size := by simp_bounds
@[simp, step_post_simps] theorem UScalar.size_UScalarTyU32 : UScalar.size .U32 = U32.size := by simp_bounds
@[simp, step_post_simps] theorem UScalar.size_UScalarTyU64 : UScalar.size .U64 = U64.size := by simp_bounds
@[simp, step_post_simps] theorem UScalar.size_UScalarTyU128 : UScalar.size .U128 = U128.size := by simp_bounds
@[simp, step_post_simps] theorem UScalar.size_UScalarTyUsize : UScalar.size .Usize = Usize.size := by simp_bounds

@[simp, step_post_simps] theorem IScalar.size_IScalarTyI8 : IScalar.size .I8 = I8.size := by simp_bounds
@[simp, step_post_simps] theorem IScalar.size_IScalarTyI16 : IScalar.size .I16 = I16.size := by simp_bounds
@[simp, step_post_simps] theorem IScalar.size_IScalarTyI32 : IScalar.size .I32 = I32.size := by simp_bounds
@[simp, step_post_simps] theorem IScalar.size_IScalarTyI64 : IScalar.size .I64 = I64.size := by simp_bounds
@[simp, step_post_simps] theorem IScalar.size_IScalarTyI128 : IScalar.size .I128 = I128.size := by simp_bounds
@[simp, step_post_simps] theorem IScalar.size_IScalarTyIsize : IScalar.size .Isize = Isize.size := by simp_bounds

@[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
theorem UScalar.toBitVec_ofBitVec {ty} : UScalar.toBitVec ∘ (@UScalar.ofBitVec ty) = id := by
  funext bv; cases ty <;> rfl

@[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
theorem U8.toBitVec_UScalar_ofBitVec : U8.bv ∘ (UScalar.ofBitVec _) = id := by rfl

@[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
theorem U16.toBitVec_UScalar_ofBitVec : U16.bv ∘ (UScalar.ofBitVec _) = id := by rfl

@[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
theorem U32.toBitVec_UScalar_ofBitVec : U32.bv ∘ (UScalar.ofBitVec _) = id := by rfl

@[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
theorem U64.toBitVec_UScalar_ofBitVec : U64.bv ∘ (UScalar.ofBitVec _) = id := by rfl

@[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
theorem U128.toBitVec_UScalar_ofBitVec : U128.bv ∘ (UScalar.ofBitVec _) = id := by rfl

@[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
theorem Usize.toBitVec_UScalar_ofBitVec : Usize.bv ∘ (UScalar.ofBitVec _) = id := by rfl

@[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
theorem IScalar.toBitVec_ofBitVec {ty} : IScalar.toBitVec ∘ (@IScalar.ofBitVec ty) = id := by
  funext bv; cases ty <;> rfl

@[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
theorem I8.toBitVec_IScalar_ofBitVec : I8.bv ∘ (IScalar.ofBitVec _) = id := by rfl

@[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
theorem I16.toBitVec_IScalar_ofBitVec : I16.bv ∘ (IScalar.ofBitVec _) = id := by rfl

@[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
theorem I32.toBitVec_IScalar_ofBitVec : I32.bv ∘ (IScalar.ofBitVec _) = id := by rfl

@[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
theorem I64.toBitVec_IScalar_ofBitVec : I64.bv ∘ (IScalar.ofBitVec _) = id := by rfl

@[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
theorem I128.toBitVec_IScalar_ofBitVec : I128.bv ∘ (IScalar.ofBitVec _) = id := by rfl

@[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
theorem Isize.toBitVec_IScalar_ofBitVec : Isize.bv ∘ (IScalar.ofBitVec _) = id := by rfl

end Std

end Aeneas
