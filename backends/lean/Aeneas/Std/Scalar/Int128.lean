
/-!
# 128-bit integer types

Lean 4.28 does not yet include `UInt128` or `Int128` in the standard library.
We define lightweight replacements that mirror the API of the official unsigned and signed types.
-/

/-- 128-bit unsigned integer, stored as a `BitVec 128`. -/
structure UInt128 where
  /-- Constructor from a `BitVec 128`. -/
  ofBitVec ::
  /-- The two's complement representation. -/
  toBitVec : BitVec 128
deriving Repr, DecidableEq

abbrev UInt128.size : Nat := 2^128

@[reducible] def UInt128.toNat (x : UInt128) : Nat := x.toBitVec.toNat
@[inline] def UInt128.ofNat (n : Nat) : UInt128 := ⟨BitVec.ofNat 128 n⟩
@[inline] def UInt128.ofNatLT (n : Nat) (h : n < UInt128.size) : UInt128 :=
  ⟨BitVec.ofNatLT n (by simpa using h)⟩

instance : OfNat UInt128 n := ⟨UInt128.ofNat n⟩
instance : Add UInt128 := ⟨fun a b => ⟨a.toBitVec + b.toBitVec⟩⟩
instance : Sub UInt128 := ⟨fun a b => ⟨a.toBitVec - b.toBitVec⟩⟩
instance : Mul UInt128 := ⟨fun a b => ⟨a.toBitVec * b.toBitVec⟩⟩
instance : Div UInt128 := ⟨fun a b => ⟨BitVec.udiv a.toBitVec b.toBitVec⟩⟩
instance : Mod UInt128 := ⟨fun a b => ⟨BitVec.umod a.toBitVec b.toBitVec⟩⟩
instance : AndOp UInt128 := ⟨fun a b => ⟨a.toBitVec &&& b.toBitVec⟩⟩
instance : OrOp UInt128 := ⟨fun a b => ⟨a.toBitVec ||| b.toBitVec⟩⟩
instance : XorOp UInt128 := ⟨fun a b => ⟨a.toBitVec ^^^ b.toBitVec⟩⟩
instance : Complement UInt128 := ⟨fun a => ⟨~~~a.toBitVec⟩⟩
instance : HShiftLeft UInt128 Nat UInt128 := ⟨fun a n => ⟨a.toBitVec <<< n⟩⟩
instance : HShiftRight UInt128 Nat UInt128 := ⟨fun a n => ⟨a.toBitVec >>> n⟩⟩
instance : LT UInt128 := ⟨fun a b => a.toBitVec < b.toBitVec⟩
instance : LE UInt128 := ⟨fun a b => a.toBitVec ≤ b.toBitVec⟩
instance : DecidableEq UInt128 := inferInstance
instance : BEq UInt128 := inferInstance
instance : LawfulBEq UInt128 := inferInstance
instance : Ord UInt128 where
  compare a b := if a.toBitVec < b.toBitVec then .lt else if a = b then .eq else .gt
instance : Inhabited UInt128 := ⟨0⟩
instance : Repr UInt128 := ⟨fun x _ => repr x.toNat⟩
instance : ToString UInt128 := ⟨fun x => toString x.toNat⟩

theorem UInt128.toBitVec_inj {a b : UInt128} : a.toBitVec = b.toBitVec ↔ a = b := by
  cases a; cases b; simp

theorem UInt128.toNat_inj {a b : UInt128} : a.toNat = b.toNat ↔ a = b := by
  simp [UInt128.toNat, ← UInt128.toBitVec_inj, ← BitVec.toNat_inj]

/-- 128-bit signed integer, stored as the two's complement `UInt128`. -/
structure Int128 where
  /-- Constructor from a `UInt128` (two's complement encoding). -/
  ofUInt128 ::
  /-- The two's complement encoding as an unsigned 128-bit integer. -/
  toUInt128 : UInt128
deriving Repr, DecidableEq

@[reducible] def Int128.toBitVec (x : Int128) : BitVec 128 := x.toUInt128.toBitVec
@[reducible] def Int128.toInt (x : Int128) : Int := x.toBitVec.toInt
@[reducible] def Int128.ofInt (i : Int) : Int128 := ⟨⟨BitVec.ofInt 128 i⟩⟩
@[reducible] def Int128.ofBitVec (b : BitVec 128) : Int128 := ⟨⟨b⟩⟩

abbrev Int128.size : Nat := 2^128
abbrev Int128.maxValue : Int128 := Int128.ofInt (2^127 - 1)
abbrev Int128.minValue : Int128 := Int128.ofInt (-(2^127))

instance : OfNat Int128 n := ⟨Int128.ofInt n⟩
instance : Neg Int128 := ⟨fun a => ⟨⟨-a.toBitVec⟩⟩⟩
instance : Add Int128 := ⟨fun a b => ⟨⟨a.toBitVec + b.toBitVec⟩⟩⟩
instance : Sub Int128 := ⟨fun a b => ⟨⟨a.toBitVec - b.toBitVec⟩⟩⟩
instance : Mul Int128 := ⟨fun a b => ⟨⟨a.toBitVec * b.toBitVec⟩⟩⟩
instance : Div Int128 := ⟨fun a b => ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩⟩
instance : Mod Int128 := ⟨fun a b => ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩⟩
instance : AndOp Int128 := ⟨fun a b => ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩⟩
instance : OrOp Int128 := ⟨fun a b => ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩⟩
instance : XorOp Int128 := ⟨fun a b => ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩⟩
instance : Complement Int128 := ⟨fun a => ⟨⟨~~~a.toBitVec⟩⟩⟩
instance : HShiftLeft Int128 Nat Int128 := ⟨fun a n => ⟨⟨a.toBitVec <<< n⟩⟩⟩
instance : HShiftRight Int128 Nat Int128 := ⟨fun a n => ⟨⟨a.toBitVec >>> n⟩⟩⟩
instance : LT Int128 := ⟨fun a b => a.toBitVec.toInt < b.toBitVec.toInt⟩
instance : LE Int128 := ⟨fun a b => a.toBitVec.toInt ≤ b.toBitVec.toInt⟩
instance : BEq Int128 := inferInstance
instance : LawfulBEq Int128 := inferInstance
instance : Ord Int128 where
  compare a b := if a.toInt < b.toInt then .lt else if a = b then .eq else .gt
instance : Inhabited Int128 := ⟨0⟩
instance : ToString Int128 := ⟨fun x => toString x.toInt⟩

@[simp] theorem Int128.ofBitVec_toBitVec (bv : BitVec 128) :
    (Int128.ofBitVec bv).toBitVec = bv := rfl

theorem Int128.toBitVec_inj {a b : Int128} : a.toBitVec = b.toBitVec ↔ a = b := by
  cases a; cases b; simp [Int128.toBitVec, UInt128.toBitVec_inj]

theorem Int128.toInt_inj {a b : Int128} : a.toInt = b.toInt ↔ a = b := by
  simp [Int128.toInt, ← Int128.toBitVec_inj, ← BitVec.toInt_inj]

theorem Int128.lt_iff_toInt_lt {x y : Int128} : x < y ↔ x.toInt < y.toInt := Iff.rfl
theorem Int128.le_iff_toInt_le {x y : Int128} : x ≤ y ↔ x.toInt ≤ y.toInt := Iff.rfl
