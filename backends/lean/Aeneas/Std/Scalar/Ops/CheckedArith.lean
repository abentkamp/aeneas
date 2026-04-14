/-
Copyright (c) Aeneas contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Checked Arithmetic Typeclasses and Notation

Aeneas maps Rust's panic-on-overflow integers to official Lean integer types (`UInt8`, `Int8`,
etc.) which already define `+`, `-`, `*` etc. as **wrapping** operations.  To avoid conflicting
`HAdd`/`HSub`/… instances, checked arithmetic that returns `Result` is spelled with the operators
`+?`, `-?`, `*?`, `/?`, `%?`.

Each operator is backed by a heterogeneous typeclass (following the `HAdd`/`HSub` pattern) so that
the result type can be in a different universe (here, `Result α`).
-/

namespace Aeneas.Std

/-- Heterogeneous checked addition: `a +? b` returns a `Result` that is `ok` when no overflow
    occurs, or `fail integerOverflow` otherwise. -/
class HCheckedAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hCheckedAdd : α → β → γ

/-- Heterogeneous checked subtraction: `a -? b` returns `fail integerOverflow` on underflow. -/
class HCheckedSub (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hCheckedSub : α → β → γ

/-- Heterogeneous checked multiplication: `a *? b` returns `fail integerOverflow` on overflow. -/
class HCheckedMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hCheckedMul : α → β → γ

/-- Heterogeneous checked division: `a /? b` returns `fail divisionByZero` when `b = 0`, or
    `fail integerOverflow` for the signed MIN / -1 case. -/
class HCheckedDiv (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hCheckedDiv : α → β → γ

/-- Heterogeneous checked remainder: `a %? b` returns `fail divisionByZero` when `b = 0`. -/
class HCheckedRem (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hCheckedRem : α → β → γ

-- Notations use the same precedence levels as standard arithmetic.
notation:65 a " +? " b:66 => HCheckedAdd.hCheckedAdd a b
notation:65 a " -? " b:66 => HCheckedSub.hCheckedSub a b
notation:70 a " *? " b:71 => HCheckedMul.hCheckedMul a b
notation:70 a " /? " b:71 => HCheckedDiv.hCheckedDiv a b
notation:70 a " %? " b:71 => HCheckedRem.hCheckedRem a b

end Aeneas.Std
