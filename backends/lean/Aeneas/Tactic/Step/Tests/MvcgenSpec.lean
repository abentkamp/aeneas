import Aeneas.Std.Scalar
import Aeneas.Std.Array
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result Std.Do
set_option mvcgen.warning false

/-!
# Tests: mvcgen spec generation from `@[step]`

For every `@[step]` theorem, the attribute handler also synthesizes an
`@[spec]` companion named `<thName>_mvcgen`. The companion lifts the Aeneas
`spec` form into a `Triple` that mvcgen consumes directly.

Sources include both the success-only form (`f x ⦃ z => P z ⦄`) and the
branch-by-branch (partial-spec) form (`f x ⦃ | ok z => ... | fail e => ... ⦄`).
-/

example {x y : U8} (hmax : x.val + y.val ≤ U8.max) :
    ⦃ ⌜ True ⌝ ⦄ (x + y) ⦃ ⇓ z => ⌜ z.val = x.val + y.val ⌝ ⦄ := by
  mvcgen; scalar_tac

example {x y : U8} :
    ⦃ ⌜ True ⌝ ⦄
      (do
        if x < 10#u8
        then x * 2#u8
        else pure y)
    ⦃ ⇓ z => ⌜ z.val ≠ y → z.val < 20 ⌝ ⦄ := by
  mvcgen <;> scalar_tac

example (arr : Array U8 25#usize) (i : Usize) (a : U8) (hi : i.val < arr.length) :
    ⦃ ⌜ True ⌝ ⦄
      Array.update arr i a
    ⦃ ⇓ r => ⌜ r = arr.set i a ⌝ ⦄ := by
  mvcgen

/-! ## Partial-spec source

The attribute also handles partial-spec sources (`⦃ | ok ... | fail ... ⦄`)
by lifting via `spec_to_mvcgen_partial` to a 3-branch `Triple`. -/

namespace partial_mvcgen_tests

def succOrPanic (b : Bool) : Result Nat :=
  match b with
  | true => ok 1
  | false => fail .panic

@[step]
theorem succOrPanic_spec (b : Bool) :
    succOrPanic b ⦃
      | ok n => n = 1 ∧ b = true
      | fail .panic => b = false
    ⦄ := by
  unfold succOrPanic Std.WP.spec
  cases b <;> simp

/-- The auto-generated `_mvcgen` companion exists and has a 3-branch post
    that exposes the partial-spec information about each Result branch. -/
example : True := by
  let _ := @succOrPanic_spec_mvcgen
  trivial

end partial_mvcgen_tests
