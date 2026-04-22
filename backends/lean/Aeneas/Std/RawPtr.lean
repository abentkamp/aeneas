import Aeneas.Std.Scalar.Core

namespace Aeneas.Std

inductive Mutability where
| Mut | Const

-- We don't really use raw pointers for now
structure RawPtr (T : Type) (M : Mutability) where
  v : T

abbrev MutRawPtr (T : Type) := RawPtr T .Mut
abbrev ConstRawPtr (T : Type) := RawPtr T .Const

inductive ScalarKind where
| Signed (ty : IScalarTy)
| Unsigned (ty : UScalarTy)

inductive IsScalar : Type → Prop where
  | u8    : IsScalar U8
  | u16   : IsScalar U16
  | u32   : IsScalar U32
  | u64   : IsScalar U64
  | u128  : IsScalar U128
  | usize : IsScalar Usize
  | i8    : IsScalar I8
  | i16   : IsScalar I16
  | i32   : IsScalar I32
  | i64   : IsScalar I64
  | i128  : IsScalar I128
  | isize : IsScalar Isize

-- TODO: we can properly define this once we have separation logic
def RawPtr.cast_scalar {T} {M} (T' : Type) (M' : Mutability)
    (_hT : IsScalar T) (_hT' : IsScalar T') (_ : RawPtr T M) :
  Result (RawPtr T' M') :=
  .fail .undef

end Aeneas.Std
