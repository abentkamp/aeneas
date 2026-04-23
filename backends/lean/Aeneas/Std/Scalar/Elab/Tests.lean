import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open ScalarElab

/-!
# Tests for two-scalar elaborators

We check that `uuscalar`, `uiscalar`, `iuscalar`, and `iiscalar` generate
definitions with the correct names and types by spot-checking representative
pairs.  `'S1`/`'S2` are substituted inline so e.g. `TestUU.from'S1_from'S2`
becomes `TestUU.fromU8_fromU8` etc.

Note: the elaborators require at least one dot in the definition name (the same
constraint that applies to the existing `uscalar`/`iscalar` commands), so all
test templates use a `Namespace.name` form.
-/

-- uuscalar: S1 ∈ unsigned, S2 ∈ unsigned (6×6 = 36 defs)
uuscalar def TestUU.from'S1_from'S2 (x : «%S2») : «%S1» := ⟨ x.bv.setWidth _ ⟩

-- Spot-check a few generated names and types.
#check @TestUU.fromU8_fromU8    -- (x : U8)   : U8
#check @TestUU.fromU16_fromU8   -- (x : U8)   : U16
#check @TestUU.fromU32_fromU16  -- (x : U16)  : U32
#check @TestUU.fromU128_fromU64 -- (x : U64)  : U128
#check @TestUU.fromUsize_fromU32 -- (x : U32) : Usize
-- Going the "wrong" direction (truncation) is also generated:
#check @TestUU.fromU8_fromU128  -- (x : U128) : U8

-- iiscalar: S1 ∈ signed, S2 ∈ signed (6×6 = 36 defs)
iiscalar def TestII.from'S1_from'S2 (x : «%S2») : «%S1» := ⟨ x.bv.setWidth _ ⟩

#check @TestII.fromI8_fromI8
#check @TestII.fromI32_fromI16
#check @TestII.fromI128_fromI64
#check @TestII.fromIsize_fromI8

-- uiscalar: S1 ∈ unsigned, S2 ∈ signed (6×6 = 36 defs)
-- Uses %BitWidth1/%BitWidth2 for the two independent bit-widths.
uiscalar def TestUI.widths'S1'S2 (_ : «%S1») (_ : «%S2») : Nat := %BitWidth1 + %BitWidth2

#check @TestUI.widthsU8I8    -- (_ : U8)  (_ : I8)  : Nat
#check @TestUI.widthsU32I64  -- (_ : U32) (_ : I64) : Nat

-- iuscalar: S1 ∈ signed, S2 ∈ unsigned (6×6 = 36 defs)
iuscalar def TestIU.widths'S1'S2 (_ : «%S1») (_ : «%S2») : Nat := %BitWidth1 + %BitWidth2

#check @TestIU.widthsI8U8
#check @TestIU.widthsIsizeU64

-- Verify the types are exactly right for key cases.
example (x : U8)  : U32  := TestUU.fromU32_fromU8 x
example (x : U64) : U128 := TestUU.fromU128_fromU64 x
example (x : I8)  : I64  := TestII.fromI64_fromI8 x

end Aeneas.Std
