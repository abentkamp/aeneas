import Lean
import Lean.Meta.Tactic.Simp
import Aeneas.Std.Core.Core
import Aeneas.Tactic.Step.Init
import Aeneas.Tactic.Solver.ScalarTac.ScalarTac
import Aeneas.Tactic.Conv.Bvify.Init
import Aeneas.Data.Nat
import Aeneas.Data.Int
import Aeneas.Tactic.Simp.SimpLists.Init
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

open Result Error ScalarElab

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

/-- Signed integer -/
structure UScalar (ty : UScalarTy) where
  /- The internal representation is a bit-vector -/
  toBitVec : BitVec ty.numBits
deriving Repr, BEq, DecidableEq

/-- Unsigned integer -/
structure IScalar (ty : IScalarTy) where
  /- The internal representation is a bit-vector -/
  toBitVec : BitVec ty.numBits
deriving Repr, BEq, DecidableEq

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

uscalar def «%S».toNat (x : «%S») : ℕ := x.toBitVec.toNat

iscalar def «%S».toInt (x : «%S») : ℤ := x.toBitVec.toInt

def U8.ofBitVec    (x : BitVec 8)                       : U8    := ⟨x⟩
def U16.ofBitVec   (x : BitVec 16)                      : U16   := ⟨x⟩
def U32.ofBitVec   (x : BitVec 32)                      : U32   := ⟨x⟩
def U64.ofBitVec   (x : BitVec 64)                      : U64   := ⟨x⟩
def U128.ofBitVec  (x : BitVec 128)                     : U128  := ⟨x⟩
def Usize.ofBitVec (x : BitVec System.Platform.numBits) : Usize := ⟨x⟩
def I8.ofBitVec    (x : BitVec 8)                       : I8    := ⟨x⟩
def I16.ofBitVec   (x : BitVec 16)                      : I16   := ⟨x⟩
def I32.ofBitVec   (x : BitVec 32)                      : I32   := ⟨x⟩
def I64.ofBitVec   (x : BitVec 64)                      : I64   := ⟨x⟩
def I128.ofBitVec  (x : BitVec 128)                     : I128  := ⟨x⟩
def Isize.ofBitVec (x : BitVec System.Platform.numBits) : Isize := ⟨x⟩

/-!
# Bounds, Size

**Remark:** we mark most constants as irreducible because otherwise it leads to issues
when using tactics like `assumption`: it often happens that unification attempts to reduce
complex expressions (for instance by trying to reduce an expression like `2^128`, which
is extremely expensive).
-/

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

/-! # Theorems -/

uscalar theorem «%S».numBits_nonzero : «%S».numBits ≠ 0 := by
  simp [numBits_def, UScalarTy.numBits] <;> cases System.Platform.numBits_eq <;> simp_all

iscalar theorem «%S».numBits_nonzero : «%S».numBits ≠ 0 := by
  simp [numBits_def]
  cases System.Platform.numBits_eq <;> grind [IScalarTy.numBits]

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
      Usize.rMax, Usize.rMax, Usize.max,
      U8.rMax, U8.max, U16.rMax, U16.max, U32.rMax, U32.max,
      U64.rMax, U64.max, U128.rMax, U128.max,
      U8.numBits, U16.numBits, U32.numBits, U64.numBits, U128.numBits, Usize.numBits,
      U8.size, U16.size, U32.size, U64.size, U128.size, Usize.size,
      Isize.rMax, Isize.rMax, Isize.max,
      I8.rMax, I8.max, I16.rMax, I16.max, I32.rMax, I32.max,
      I64.rMax, I64.max, I128.rMax, I128.max,
      Isize.rMin, Isize.rMin, Isize.min,
      I8.rMin, I8.min, I16.rMin, I16.min, I32.rMin, I32.min,
      I64.rMin, I64.min, I128.rMin, I128.min,
      I8.numBits, I16.numBits, I32.numBits, I64.numBits, I128.numBits, Isize.numBits,
      I8.size, I16.size, I32.size, I64.size, I128.size, Isize.size])

theorem Usize.bounds_eq :
  Usize.max = U32.max ∨ Usize.max = U64.max := by
  simp [Usize.max, Usize.numBits]
  cases System.Platform.numBits_eq <;>
  simp [*] <;>
  simp_bounds

grind_pattern Usize.bounds_eq => Usize.max
grind_pattern [agrind] Usize.bounds_eq => Usize.max

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

uscalar theorem «%S».rMax_eq_max : rMax = max := by simp_bounds

iscalar theorem «%S».rbound_eq_bound :
  rMin = «%S».min ∧ rMax = max := by
  split_conjs <;> simp_bounds

iscalar theorem «%S».rMin_eq_min : rMin = min := by
  apply «%S».rbound_eq_bound.left

iscalar theorem «%S».rMax_eq_max : rMax = max := by
  apply «%S».rbound_eq_bound.right

/-!
# "Conservative" Bounds

We use those because we can't compare to the isize bounds (which can't
reduce at compile-time). Whenever we perform an arithmetic operation like
addition we need to check that the result is in bounds: we first compare
to the conservative bounds, which reduces, then compare to the real bounds.

This is useful for the various #asserts that we want to reduce at
type-checking time, or when defining constants.
-/

uscalar_no_usize def «%S».cNumBits : Nat := «%S».numBits
def Usize.cNumBits : Nat := U32.numBits

iscalar_no_isize def «%S».cNumBits : Nat := «%S».numBits
def Isize.cNumBits : Nat := I32.numBits

uscalar theorem «%S».cNumBits_le : «%S».cNumBits ≤ «%S».numBits := by
  simp only [cNumBits, U32.numBits, «%S».numBits_def, UScalarTy.numBits, System.Platform.le_numBits, le_refl]

iscalar theorem «%S».cNumBits_le : «%S».cNumBits ≤ «%S».numBits := by
  simp only [cNumBits, I32.numBits, numBits, IScalarTy.numBits, System.Platform.le_numBits, le_refl, numBits_def]

uscalar theorem «%S».cNumBits_nonzero : «%S».cNumBits ≠ 0 := by
  simp [cNumBits, U32.numBits, numBits_def]

iscalar theorem «%S».cNumBits_nonzero : «%S».cNumBits ≠ 0 := by
  simp [cNumBits, I32.numBits, numBits_def]

uscalar_no_usize def «%S».cMax : Nat := «%S».rMax
def Usize.cMax : Nat := U32.rMax

iscalar_no_isize def «%S».cMin : Int := «%S».rMin
def Isize.cMin : Int := I32.rMin

iscalar_no_isize def «%S».cMax : Int := «%S».rMax
def Isize.cMax : Int := I32.rMax

uscalar @[grind ., agrind .]
theorem «%S».hBounds (x : «%S») : x.toNat < 2^«%S».numBits := by
  cases h: x.toBitVec
  simp only [toNat, h, BitVec.toNat_ofFin, Fin.is_lt, numBits_def]

uscalar theorem «%S».hSize (x : «%S») : x.toNat < «%S».size := by
  cases h: x.toBitVec
  simp [h, toNat, size, numBits_def]

uscalar theorem «%S».rMax_eq_pow_numBits :  «%S».rMax = 2 ^ «%S».numBits - 1 := by
  simp [rMax]; simp_bounds

uscalar theorem «%S».cMax_eq_pow_cNumBits : «%S».cMax = 2^«%S».cNumBits - 1 := by
  simp [cMax, cNumBits]; simp_bounds

uscalar theorem «%S».cMax_le_rMax : «%S».cMax ≤ «%S».rMax := by
  have := rMax_eq_pow_numBits
  have := cMax_eq_pow_cNumBits
  have := cNumBits_le
  have := @Nat.pow_le_pow_right 2 (by simp) cNumBits numBits cNumBits_le
  omega

uscalar theorem «%S».hrBounds (x : «%S») : x.toNat ≤ «%S».rMax := by
  have := hBounds x
  have := rMax_eq_pow_numBits
  omega


uscalar theorem «%S».hmax (x : «%S») : x.toNat < 2^«%S».numBits := x.hBounds

iscalar theorem «%S».hBounds (x : «%S») :
  -2^(numBits - 1) ≤ x.toInt ∧ x.toInt < 2^(numBits - 1) := by
  match x with
  | ⟨ ⟨ fin ⟩ ⟩ =>
    simp [toInt, BitVec.toInt]
    have hFinLt := fin.isLt
    cases h: System.Platform.numBits_eq <;>
    simp_all only [IScalarTy.Isize_numBits_eq, true_or] <;>
    simp_all only [numBits_def, IScalarTy.numBits] <;>
    omega

iscalar theorem «%S».rMin_eq_pow_numBits : «%S».rMin = -2^(«%S».numBits - 1) := by
  simp [numBits_def]; simp_bounds

iscalar theorem «%S».rMax_eq_pow_numBits : «%S».rMax = 2^(«%S».numBits - 1) - 1 := by
  simp [rMax]; simp_bounds

iscalar theorem «%S».cMin_eq_pow_cNumBits : «%S».cMin = -2^(«%S».cNumBits - 1) := by
  simp [cMin, cNumBits]; simp_bounds

iscalar theorem «%S».cMax_eq_pow_cNumBits : cMax = 2^(cNumBits - 1) - 1 := by
  simp [cMax, cNumBits]; simp_bounds

iscalar theorem «%S».rMin_le_cMin : «%S».rMin ≤ «%S».cMin := by
  have := rMin_eq_pow_numBits
  have := cMin_eq_pow_cNumBits
  have := cNumBits_le
  have := cNumBits_nonzero
  have := @Nat.pow_le_pow_right 2 (by simp) (cNumBits - 1) (numBits - 1) (by omega)
  zify at this
  omega

iscalar theorem «%S».cMax_le_rMax : «%S».cMax ≤ «%S».rMax := by
  have := rMax_eq_pow_numBits
  have := cMax_eq_pow_cNumBits
  have := cNumBits_le
  have := cNumBits_nonzero
  have := @Nat.pow_le_pow_right 2 (by simp) (cNumBits - 1) (numBits - 1) (by omega)
  zify at this
  omega

iscalar def «%S».hmin (x : «%S») : -2^(numBits - 1) ≤ x.toInt := x.hBounds.left
iscalar def «%S».hmax (x : «%S») : x.toInt < 2^(numBits - 1) := x.hBounds.right

scalar instance : BEq «%S» where
  beq a b := a.toBitVec = b.toBitVec

instance {ty} : BEq (UScalar ty) where
  beq a b := a.toBitVec = b.toBitVec

instance {ty} : BEq (IScalar ty) where
  beq a b := a.toBitVec = b.toBitVec

scalar instance : LawfulBEq «%S» where
  eq_of_beq {a b} := by cases a; cases b; simp [BEq.beq]
  rfl {a} := by cases a; simp [BEq.beq]

instance {ty} : LawfulBEq (UScalar ty) where
  eq_of_beq {a b} := by cases a; cases b; simp [BEq.beq]
  rfl {a} := by cases a; simp [BEq.beq]

instance {ty} : LawfulBEq (IScalar ty) where
  eq_of_beq {a b} := by cases a; cases b; simp[BEq.beq]
  rfl {a} := by cases a; simp [BEq.beq]

uscalar instance : CoeOut «%S» Nat where
  coe := λ v => v.toNat

iscalar instance : CoeOut «%S» Int where
  coe := λ v => v.toInt

/- Activate the ↑ notation -/
uscalar attribute [coe] «%S».toNat
iscalar attribute [coe] «%S».toInt

uscalar theorem «%S».bound_suffices (x : Nat) :
  x ≤ cMax -> x < 2^numBits := by
  intro h
  have := rMax_eq_pow_numBits
  have : 0 < 2^numBits := by simp
  have := cMax_le_rMax
  omega

iscalar theorem «%S».bound_suffices (x : Int) :
  «%S».cMin ≤ x ∧ x ≤ «%S».cMax ->
  -2^(«%S».numBits - 1) ≤ x ∧ x < 2^(«%S».numBits - 1)
  := by
  intro h
  have := «%S».cNumBits_nonzero
  have := «%S».numBits_nonzero
  have := «%S».cNumBits_le
  have := «%S».rMin_eq_pow_numBits
  have := «%S».rMax_eq_pow_numBits
  have := rMin_le_cMin
  have := cMax_le_rMax
  omega

uscalar def «%S».ofNatCore (x : Nat) (h : x < 2^numBits) : «%S» :=
  have h : x < 2 ^ UScalarTy.«%S».numBits := by grind [numBits_def]
  { toBitVec := ⟨ x, h ⟩ }

iscalar def «%S».ofIntCore (x : Int) (_ : -2^(numBits-1) ≤ x ∧ x < 2^(numBits - 1)) : «%S» :=
  -- TODO: we should leave `x` unchanged if it is positive, so that expressions like `(1#isize).toInt` can reduce to `1`
  let x' := (x % 2^IScalarTy.«%S».numBits).toNat
  have h : x' < 2^IScalarTy.«%S».numBits := by
    zify
    simp +zetaDelta only [Int.ofNat_toNat, sup_lt_iff, Nat.ofNat_pos, pow_pos, and_true]
    apply Int.emod_lt_of_pos; simp
  { toBitVec := ⟨ x', h ⟩ }

uscalar @[reducible] def «%S».ofNat (x : Nat)
  (hInBounds : x ≤ «%S».cMax := by decide) : «%S» :=
  «%S».ofNatCore x («%S».bound_suffices x hInBounds)

iscalar @[reducible] def «%S».ofInt (x : Int)
  (hInBounds : «%S».cMin ≤ x ∧ x ≤ «%S».cMax := by decide) : «%S» :=
  «%S».ofIntCore x («%S».bound_suffices x hInBounds)

uscalar @[simp] abbrev «%S».inBounds (x : Nat) : Prop :=
  x < 2^numBits

iscalar @[simp] abbrev «%S».inBounds (x : Int) : Prop :=
  - 2^(numBits - 1) ≤ x ∧ x < 2^(numBits - 1)

uscalar @[simp] abbrev «%S».check_bounds (x : Nat) : Bool :=
  x < 2^numBits

iscalar @[simp] abbrev «%S».check_bounds (x : Int) : Bool :=
  - 2^(numBits - 1) ≤ x ∧ x < 2^(numBits - 1)

uscalar theorem «%S».check_bounds_imp_inBounds {x : Nat}
  (h: «%S».check_bounds x) :
  «%S».inBounds x := by
  simp at *; apply h

uscalar theorem  «%S».check_bounds_eq_inBounds (x : Nat) :
  «%S».check_bounds x ↔ «%S».inBounds x := by
  constructor <;> intro h
  . apply (check_bounds_imp_inBounds h)
  . simp_all

iscalar theorem «%S».check_bounds_imp_inBounds {x : Int}
  (h: «%S».check_bounds x) :
  «%S».inBounds x := by
  simp at *; apply h

iscalar theorem «%S».check_bounds_eq_inBounds (x : Int) :
  «%S».check_bounds x ↔ «%S».inBounds x := by
  constructor <;> intro h
  . apply (check_bounds_imp_inBounds h)
  . simp_all

uscalar def «%S».tryMkOpt (x : Nat) : Option «%S» :=
  if h:check_bounds x then
    some («%S».ofNatCore x («%S».check_bounds_imp_inBounds h))
  else none

uscalar def «%S».tryMk (x : Nat) : Result «%S» :=
  Result.ofOption (tryMkOpt x) integerOverflow

iscalar def «%S».tryMkOpt (x : Int) : Option «%S» :=
  if h:check_bounds x then
    some («%S».ofIntCore x («%S».check_bounds_imp_inBounds h))
  else none

iscalar def «%S».tryMk (x : Int) : Result «%S» :=
  Result.ofOption (tryMkOpt x) integerOverflow

uscalar theorem «%S».tryMkOpt_eq (x : Nat) :
  match tryMkOpt x with
  | some y => y.toNat = x ∧ inBounds x
  | none => ¬ (inBounds x) := by
  simp [tryMkOpt, «%S».ofNatCore]
  have h := check_bounds_eq_inBounds x
  split_ifs <;> simp_all
  simp [toNat] at *

uscalar theorem «%S».tryMk_eq (x : Nat) :
  match tryMk x with
  | ok y => y.toNat = x ∧ inBounds x
  | fail _ => ¬ (inBounds x)
  | _ => False := by
  have := tryMkOpt_eq x
  simp [tryMk, ofOption]
  cases h: tryMkOpt x <;> simp_all

iscalar theorem «%S».tryMkOpt_eq (x : Int) :
  match tryMkOpt x with
  | some y => y.toInt = x ∧ inBounds x
  | none => ¬ (inBounds x) := by
  simp [tryMkOpt, «%S».ofIntCore]
  have h := check_bounds_eq_inBounds x
  split_ifs <;> simp_all [numBits_def]
  simp [toInt] at *
  simp [Int.bmod]; split <;> (try omega) <;>
  cases h: System.Platform.numBits_eq <;> simp_all <;> omega

iscalar theorem «%S».tryMk_eq (x : Int) :
  match «%S».tryMk x with
  | ok y => y.toInt = x ∧ inBounds x
  | fail _ => ¬ (inBounds x)
  | _ => False := by
  have := tryMkOpt_eq x
  simp [tryMk]
  cases h : tryMkOpt x <;> simp_all

uscalar @[simp] theorem «%S».zero_in_cbounds : 0 < 2^numBits := by simp

iscalar @[simp] theorem «%S».zero_in_cbounds :
  -2^(numBits - 1) ≤ 0 ∧ 0 < 2^(numBits - 1) := by simp

uscalar @[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =]
theorem «%S».ofNatCore_toNat_eq {x} (h) :
  («%S».ofNatCore x h).toNat = x := by
  simp [ofNatCore, toNat]

iscalar @[simp, scalar_tac_simps, bvify, grind =, agrind =]
theorem «%S».ofInt_toInt_eq (h : -2^(numBits-1) ≤ x ∧ x < 2^(numBits-1)) :
  («%S».ofIntCore x h).toInt = x := by
  simp [«%S».ofIntCore, toInt]
  simp_all [numBits_def];
  simp [Int.bmod]; split <;> (try omega) <;>
  cases h: System.Platform.numBits_eq <;> simp_all <;> omega

uscalar @[bvify] theorem «%S».eq_equiv_toBitVec_eq (x y : «%S») :
    x = y ↔ x.toBitVec = y.toBitVec := by
  cases x; cases y; simp

uscalar @[ext, grind ext, agrind ext]
theorem «%S».toBitVec_eq_imp_eq (x y : «%S») : x.toBitVec = y.toBitVec → x = y := by
  simp [eq_equiv_toBitVec_eq]

uscalar theorem «%S».ofNatCore_toBitVec (x : Nat) h :
  («%S».ofNatCore x h).toBitVec = BitVec.ofNat _ x := by
  congr; rw [Nat.mod_eq_of_lt]; rwa [numBits_def] at *

uscalar @[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =]
theorem «%S».ofNat_toBitVec (x : Nat) (h) : («%S».ofNat x h).toBitVec = BitVec.ofNat _ x := by
  apply «%S».ofNatCore_toBitVec

iscalar @[bvify] theorem «%S».eq_equiv_toBitVec_eq (x y : «%S») :
    x = y ↔ x.toBitVec = y.toBitVec := by
  cases x; cases y; simp

iscalar @[ext, grind ext, agrind ext] theorem «%S».toBitVec_eq_imp_eq (x y : «%S») :
    x.toBitVec = y.toBitVec → x = y := by
  simp[eq_equiv_toBitVec_eq]

iscalar theorem «%S».ofIntCore_toBitVec (x : Int) h :
  («%S».ofIntCore x h).toBitVec = BitVec.ofInt _ x := by
  simp only [ofIntCore, BitVec.ofInt, Int.ofNat_eq_natCast, Nat.cast_pow, Nat.cast_ofNat, IScalarTy.numBits, numBits]
  congr

iscalar @[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind =, agrind =]
theorem «%S».ofInt_toBitVec (x : Int) h : («%S».ofInt x h).toBitVec = BitVec.ofInt _ x :=
  «%S».ofIntCore_toBitVec x
    (by grind [rMin_le_cMin, cMax_le_rMax, rMax_eq_pow_numBits, rMin_eq_pow_numBits])

uscalar instance : Inhabited «%S» := by
  constructor; apply («%S».ofNat 0 (by simp))

iscalar instance : Inhabited «%S» := by
  constructor; apply («%S».ofInt 0 (by simp [«%S».cMin, «%S».cMax]; simp_bounds))

uscalar @[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem «%S».default_toNat : (default : «%S»).toNat = 0 := by
  simp only [default]; simp

uscalar @[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem «%S».default_toBitVec : (default : «%S»).toBitVec = 0 := by
  simp only [default]; simp

iscalar theorem «%S».min_lt_max : «%S».min < «%S».max := by
  have : (0 : Int) < 2 ^ (System.Platform.numBits - 1) := by simp
  simp [«%S».min, «%S».max]; (try simp_bounds) <;> omega

iscalar theorem «%S».min_le_max : «%S».min ≤ «%S».max := by
  have := «%S».min_lt_max
  scalar_tac

uscalar_no_usize @[reducible] def core.num.«%S».MIN : «%S» := «%S».ofNat 0
uscalar_no_usize @[reducible] def core.num.«%S».MAX : «%S» := «%S».ofNat «%S».rMax
@[reducible] def core.num.Usize.MIN : Usize := Usize.ofNatCore 0 (by simp)
@[reducible] def core.num.Usize.MAX : Usize := Usize.ofNatCore Usize.max (by simp [Usize.max, Usize.numBits])

iscalar_no_isize @[reducible] def core.num.«%S».MIN : «%S» := «%S».ofInt «%S».rMin
iscalar_no_isize @[reducible] def core.num.«%S».MAX : «%S» := «%S».ofInt «%S».rMax
@[reducible] def core.num.Isize.MIN : Isize := Isize.ofIntCore Isize.min (by simp [Isize.min, Isize.numBits])
@[reducible] def core.num.Isize.MAX : Isize := Isize.ofIntCore Isize.max (by simp [Isize.max, Isize.numBits]; (have : (0 : Int) < 2 ^ (System.Platform.numBits - 1) := by simp); omega)


/-! # Comparisons -/
uscalar instance : LT «%S» where
  lt a b := LT.lt a.toNat b.toNat

uscalar instance : LE «%S» where le a b := LE.le a.toNat b.toNat

iscalar instance : LT «%S» where
  lt a b := LT.lt a.toInt b.toInt

iscalar instance : LE «%S» where le a b := LE.le a.toInt b.toInt

/- Not marking this one with @[simp] on purpose: if we have `x = y` somewhere in the context,
   we may want to use it to substitute `y` with `x` somewhere. -/
/- Not marking this one with @[simp] on purpose: if we have `x = y` somewhere in the context,
   we may want to use it to substitute `y` with `x` somewhere. -/
uscalar @[scalar_tac_simps, zify_simps] theorem «%S».eq_equiv (x y : «%S») :
  x = y ↔ (↑x : Nat) = ↑y := by
  cases x; cases y; simp_all [toNat, BitVec.toNat_eq]

uscalar @[ext, grind ext, agrind ext] theorem «%S».toNat_eq_imp (x y : «%S») :
  (↑x : Nat) = ↑y → x = y := by
  simp [eq_equiv]

uscalar theorem «%S».eq_imp (x y : «%S») :
  (↑x : Nat) = ↑y → x = y := (eq_equiv x y).mpr

uscalar @[simp, scalar_tac_simps, grind =, agrind =, zify_simps]
theorem «%S».lt_equiv (x y : «%S») :
  x < y ↔ (↑x : Nat) < ↑y := by
  rw [LT.lt, instLT'S]

uscalar @[simp] theorem «%S».lt_imp (x y : «%S») :
  (↑x : Nat) < (↑y) → x < y := (lt_equiv x y).mpr

uscalar @[simp, scalar_tac_simps, grind =, agrind =, zify_simps]
theorem «%S».le_equiv (x y : «%S») :
  x ≤ y ↔ (↑x : Nat) ≤ ↑y := by
  rw [LE.le, instLE'S]

uscalar @[simp] theorem «%S».le_imp (x y : «%S») :
  (↑x : Nat) ≤ ↑y → x ≤ y := (le_equiv x y).mpr

iscalar @[scalar_tac_simps, zify_simps] theorem «%S».eq_equiv (x y : «%S») :
  x = y ↔ (↑x : Int) = ↑y := by
  cases x; cases y; simp_all [toInt]
  constructor <;> intro <;>
  first | simp [*] | apply BitVec.eq_of_toInt_eq; simp [*]

iscalar @[ext, grind ext, agrind ext]
theorem «%S».toInt_eq_imp (x y : «%S») :
  (↑x : Int) = ↑y → x = y := by
  simp [eq_equiv]

iscalar theorem «%S».eq_imp (x y : «%S») :
  (↑x : Int) = ↑y → x = y := (eq_equiv x y).mpr

iscalar @[simp, scalar_tac_simps, grind =, agrind =, zify_simps]
theorem «%S».lt_equiv (x y : «%S») :
  x < y ↔ (↑x : Int) < ↑y := by
  rw [LT.lt, instLT'S]

iscalar @[simp, scalar_tac_simps] theorem «%S».lt_imp (x y : «%S») :
  (↑x : Int) < (↑y) → x < y := (lt_equiv x y).mpr

iscalar @[simp, scalar_tac_simps, grind =, agrind =, zify_simps]
theorem «%S».le_equiv (x y : «%S») :
  x ≤ y ↔ (↑x : Int) ≤ ↑y := by simp [LE.le]

iscalar @[simp] theorem «%S».le_imp (x y : «%S») :
  (↑x : Int) ≤ ↑y → x ≤ y := (le_equiv x y).mpr

uscalar instance «%S».decLt (a b : «%S») : Decidable (LT.lt a b) := Nat.decLt ..
uscalar instance «%S».decLe (a b : «%S») : Decidable (LE.le a b) := Nat.decLe ..
iscalar instance «%S».decLt (a b : «%S») : Decidable (LT.lt a b) := Int.decLt ..
iscalar instance «%S».decLe (a b : «%S») : Decidable (LE.le a b) := Int.decLe ..

uscalar theorem «%S».eq_of_toNat_eq : ∀ {i j : «%S»}, Eq i.toNat j.toNat → Eq i j
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

iscalar theorem «%S».eq_of_toInt_eq : ∀ {i j : «%S»}, Eq i.toInt j.toInt → Eq i j := by
  intro i j hEq
  cases i; cases j
  simp [toInt] at hEq; simp
  apply BitVec.eq_of_toInt_eq; assumption

uscalar theorem «%S».toNat_eq_of_eq {i j : «%S»} (h : Eq i j) : Eq i.toNat j.toNat := h ▸ rfl

iscalar theorem «%S».toInt_eq_of_eq {i j : «%S»} (h : Eq i j) : Eq i.toInt j.toInt := h ▸ rfl

uscalar theorem «%S».ne_of_toNat_ne {i j : «%S»} (h : Not (Eq i.toNat j.toNat)) : Not (Eq i j) :=
  fun h' => absurd («%S».toNat_eq_of_eq h') h

iscalar theorem «%S».ne_of_toInt_ne {i j : «%S»} (h : Not (Eq i.toInt j.toInt)) : Not (Eq i j) :=
  fun h' => absurd («%S».toInt_eq_of_eq h') h

uscalar instance : DecidableEq «%S» :=
  fun i j =>
    match decEq i.toNat j.toNat with
    | isTrue h  => isTrue («%S».eq_of_toNat_eq h)
    | isFalse h => isFalse («%S».ne_of_toNat_ne h)

iscalar instance : DecidableEq «%S» :=
  fun i j =>
    match decEq i.toInt j.toInt with
    | isTrue h  => isTrue («%S».eq_of_toInt_eq h)
    | isFalse h => isFalse («%S».ne_of_toInt_ne h)

uscalar @[simp, scalar_tac_simps]
theorem «%S».neq_to_neq_toNat :
  ∀ {i j : «%S»}, (¬ i = j) ↔ ¬ i.toNat = j.toNat := by
  simp [«%S».eq_equiv, toNat]

iscalar @[simp, scalar_tac_simps]
theorem «%S».neq_to_neq_toInt :
  ∀ {i j : «%S»}, (¬ i = j) ↔ ¬ i.toInt = j.toInt := by
  simp [«%S».eq_equiv, toInt]

uscalar @[simp]
theorem «%S».toNat_not_eq_imp_not_eq (x y : «%S») (h : Nat.not_eq x.toNat y.toNat) :
  ¬ x = y := by
  simp_all [toNat]; scalar_tac

iscalar @[simp]
theorem «%S».toInt_not_eq_imp_not_eq (x y : «%S») (h : Int.not_eq x.toInt y.toInt) :
  ¬ x = y := by
  simp_all [toInt]; scalar_tac

uscalar instance : Preorder «%S» where
  le_refl := fun a => by simp
  le_trans := fun a b c => by
    intro Hab Hbc
    exact (le_trans (((«%S».le_equiv _ _)).1 Hab) (((«%S».le_equiv _ _)).1 Hbc))
  lt_iff_le_not_ge := fun a b => by
    trans (a: Nat) < (b: Nat); exact («%S».lt_equiv _ _)
    trans (a: Nat) ≤ (b: Nat) ∧ ¬ (b: Nat) ≤ (a: Nat); exact lt_iff_le_not_ge
    rw [← «%S».le_equiv]; rfl

iscalar instance : Preorder «%S» where
  le_refl := fun a => by simp
  le_trans := fun a b c => by
    intro Hab Hbc
    exact (le_trans (((«%S».le_equiv _ _)).1 Hab) (((«%S».le_equiv _ _)).1 Hbc))
  lt_iff_le_not_ge := fun a b => by
    trans (a: Int) < (b: Int); exact («%S».lt_equiv _ _)
    trans (a: Int) ≤ (b: Int) ∧ ¬ (b: Int) ≤ (a: Int); exact lt_iff_le_not_ge
    rw [← «%S».le_equiv]; rfl

uscalar instance : PartialOrder «%S» where
  le_antisymm := fun a b Hab Hba =>
    «%S».eq_imp _ _ ((@le_antisymm Nat _ _ _ ((«%S».le_equiv a b).1 Hab) ((«%S».le_equiv b a).1 Hba)))

iscalar instance : PartialOrder «%S» where
  le_antisymm := fun a b Hab Hba =>
    «%S».eq_imp _ _ ((@le_antisymm Int _ _ _ ((«%S».le_equiv a b).1 Hab) ((«%S».le_equiv b a).1 Hba)))

uscalar instance «'SDecidableLE» : DecidableRel (· ≤ · : «%S» -> «%S» -> Prop) := by
  simp
  -- Lift this to the decidability of the Int version.
  infer_instance

iscalar instance «'SDecidableLE» : DecidableRel (· ≤ · : «%S» -> «%S» -> Prop) := by
  simp
  -- Lift this to the decidability of the Int version.
  infer_instance

uscalar instance : LinearOrder «%S» where
  le_total := fun a b => by
    rcases (Nat.le_total a b) with H | H
    left; exact («%S».le_equiv _ _).2 H
    right; exact («%S».le_equiv _ _).2 H
  toDecidableLE := inferInstance

iscalar instance : LinearOrder «%S» where
  le_total := fun a b => by
    rcases (Int.le_total a b) with H | H
    left; exact («%S».le_equiv _ _).2 H
    right; exact («%S».le_equiv _ _).2 H
  toDecidableLE := inferInstance

/-! # Coercion Theorems

    This is helpful whenever you want to "push" casts to the innermost nodes
    and make the cast normalization happen more magically. -/

uscalar @[simp, norm_cast, scalar_tac_simps, grind =, agrind =]
theorem «%S».coe_max (a b : «%S»): ↑(Max.max a b) = (Max.max (↑a) (↑b): ℕ) := by
  rw[_root_.max_def, _root_.max_def]
  split_ifs <;> simp_all

iscalar @[simp, norm_cast, scalar_tac_simps, grind =, agrind =]
theorem «%S».coe_max (a b : «%S»): ↑(Max.max a b) = (Max.max (↑a) (↑b): ℤ) := by
  rw[_root_.max_def, _root_.max_def]
  split_ifs <;> simp_all [toInt]; omega

/-! Max theory -/
-- TODO: do the min theory later on.

uscalar theorem «%S».zero_le (x: «%S»): «%S».ofNat 0 (by simp) ≤ x := by simp

uscalar @[simp]
theorem «%S».max_left_zero_eq (x : «%S»):
  Max.max («%S».ofNat 0 (by simp)) x = x := max_eq_right («%S».zero_le x)

uscalar @[simp]
theorem «%S».max_right_zero_eq (x : «%S»):
  Max.max x («%S».ofNat 0 (by simp)) = x := max_eq_left («%S».zero_le x)

/-! Some conversions -/
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind, agrind] abbrev I8.toNat      (x : I8) : Nat := x.toInt.toNat
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind, agrind] abbrev I16.toNat     (x : I16) : Nat := x.toInt.toNat
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind, agrind] abbrev I32.toNat     (x : I32) : Nat := x.toInt.toNat
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind, agrind] abbrev I64.toNat     (x : I64) : Nat := x.toInt.toNat
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind, agrind] abbrev I128.toNat    (x : I128) : Nat := x.toInt.toNat
@[simp, scalar_tac_simps, simp_scalar_safe, bvify, grind, agrind] abbrev Isize.toNat   (x : Isize) : Nat := x.toInt.toNat

abbrev U8.toBitVec (x : U8)   : BitVec 8 := x.1
abbrev U16.toBitVec (x : U16) : BitVec 16 := x.1
abbrev U32.toBitVec (x : U32) : BitVec 32 := x.1
abbrev U64.toBitVec (x : U64) : BitVec 64 := x.1
abbrev U128.toBitVec (x : U128) : BitVec 128 := x.1
abbrev Usize.toBitVec (x : Usize) : BitVec System.Platform.numBits := x.1

abbrev I8.toBitVec (x : I8) : BitVec 8 := x.1
abbrev I16.toBitVec (x : I16) : BitVec 16 := x.1
abbrev I32.toBitVec (x : I32) : BitVec 32 := x.1
abbrev I64.toBitVec (x : I64) : BitVec 64 := x.1
abbrev I128.toBitVec (x : I128) : BitVec 128 := x.1
abbrev Isize.toBitVec (x : Isize) : BitVec System.Platform.numBits := x.1

uscalar @[simp, scalar_tac_simps, grind =, agrind =]
theorem «%S».toBitVec_toNat (x : «%S») : x.toBitVec.toNat = x.toNat := by
  simp [toNat]

iscalar @[simp, scalar_tac_simps, grind =, agrind =]
theorem «%S».toBitVec_toInt_eq (x : «%S») : x.toBitVec.toInt = x.toInt := by
  simp [toInt]

@[bvify] theorem U8.lt_succ_max (x: U8) : x.toNat < 256 := by have := x.hBounds; simp [numBits_def] at this; omega
@[bvify] theorem U16.lt_succ_max (x: U16) : x.toNat < 65536 := by have := x.hBounds; simp [numBits_def] at this; omega
@[bvify] theorem U32.lt_succ_max (x: U32) : x.toNat < 4294967296 := by have := x.hBounds; simp [numBits_def] at this; omega
@[bvify] theorem U64.lt_succ_max (x: U64) : x.toNat < 18446744073709551616 := by have := x.hBounds; simp [numBits_def] at this; omega
@[bvify] theorem U128.lt_succ_max (x: U128) : x.toNat < 340282366920938463463374607431768211456 := by have := x.hBounds; simp [numBits_def] at this; omega

@[bvify] theorem U8.le_max (x: U8) : x.toNat ≤ 255 := by have := x.hBounds; simp [numBits_def] at this; omega
@[bvify] theorem U16.le_max (x: U16) : x.toNat ≤ 65535 := by have := x.hBounds; simp [numBits_def] at this; omega
@[bvify] theorem U32.le_max (x: U32) : x.toNat ≤ 4294967295 := by have := x.hBounds; simp [numBits_def] at this; omega
@[bvify] theorem U64.le_max (x: U64) : x.toNat ≤ 18446744073709551615 := by have := x.hBounds; simp [numBits_def] at this; omega
@[bvify] theorem U128.le_max (x: U128) : x.toNat ≤ 340282366920938463463374607431768211455 := by have := x.hBounds; simp [numBits_def] at this; omega

uscalar @[simp, scalar_tac_simps, grind =, agrind =]
theorem «%S».ofNat_self_toNat (x : «%S») (hInBounds : x.toNat ≤ cMax) :
  «%S».ofNat x hInBounds = x := eq_of_toNat_eq rfl

iscalar @[simp, scalar_tac_simps, grind =, agrind =]
theorem «%S».ofInt_toInt (x : «%S») (hInBounds : cMin ≤ x.toInt ∧ x.toInt ≤ cMax) :
  «%S».ofInt x hInBounds = x := by simp only [ofInt, eq_equiv]; apply ofInt_toInt_eq

uscalar @[simp, bvify]
theorem «%S».BitVec_ofNat_toNat (x : «%S») : BitVec.ofNat %BitWidth x.toNat = x.toBitVec := by
  cases x; simp only [toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, UScalarTy.numBits]

iscalar @[simp, bvify]
theorem «%S».BitVec_ofInt_toInt (x : «%S») : BitVec.ofInt %BitWidth x.toInt = x.toBitVec := by
  cases x; simp only [toInt, BitVec.ofInt_toInt]

uscalar @[simp, bvify]
theorem «%S».Nat_cast_BitVec_toNat (x : «%S») : Nat.cast x.toNat = x.toBitVec := by
  simp only [BitVec.natCast_eq_ofNat, «%S».BitVec_ofNat_toNat]

iscalar @[simp, bvify]
theorem «%S».Nat_cast_BitVec_toInt (x : «%S») : Int.cast x.toInt = x.toBitVec := by
  simp only [Int.cast, IntCast.intCast, «%S».BitVec_ofInt_toInt]

/-!
Adding theorems to the `zify_simps` simplification set.
-/
attribute [zify_simps] U8.toBitVec_toNat U16.toBitVec_toNat U32.toBitVec_toNat
                       U64.toBitVec_toNat U128.toBitVec_toNat Usize.toBitVec_toNat

scalar @[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
theorem «%S».toBitVec_mk : «%S».toBitVec ∘ «%S».ofBitVec = id := by rfl

uscalar @[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe, grind =, agrind =]
theorem «%S».toNat_ofBitVec (x : BitVec %BitWidth) :
  «%S».toNat («%S».ofBitVec x) = x.toNat := Nat.add_zero (ofBitVec x).toBitVec.toFin.1

iscalar @[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe, grind =, agrind =]
theorem «%S».toInt_ofBitVec (x : BitVec %BitWidth) :
  «%S».toInt («%S».ofBitVec x) = x.toInt := Int.neg_inj.mp rfl

scalar @[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe, grind =, agrind =]
theorem «%S».toBitVec_ofBitVec (x : BitVec %BitWidth) :
  («%S».ofBitVec x).toBitVec = x := by rfl

end Std

end Aeneas
