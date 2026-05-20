import Aeneas.Std.Scalar
import Aeneas.Tactic.Step

/-!
# Tests: `@[step]` accepts `spec_partial` lemmas

For a theorem using `spec_partial`, marking it with `@[step]` should register it for `step*` and
for `mvcgen`.
-/

namespace Aeneas.Step.SpecPartialTests

open Aeneas Aeneas.Std Result Std.Do WP

set_option mvcgen.warning false

opaque myDiv (x y : U32) : Result U32

@[step]
axiom myDiv_spec_partial (x y : U32) :
  spec_partial (myDiv x y)
    (fun z => z.val = x.val / y.val)
    (fun _ => y.val = 0)
    False

/-- step* -/
example (x y : U32) (h : y.val ≠ 0) :
    spec (myDiv x y) (fun z => z.val = x.val / y.val) := by
  step*

/-- mvcgen: total correctness -/
example (x y : U32) (h : y.val ≠ 0) :
    ⦃ ⌜ True ⌝ ⦄ (myDiv x y) ⦃ ⇓ z => ⌜ z.val = x.val / y.val ⌝ ⦄ := by
  mvcgen

/-- mvcgen: partial correctness -/
example (x y : U32) :
    ⦃ ⌜ True ⌝ ⦄ (myDiv x y) ⦃ ⇓? z => ⌜ z.val = x.val / y.val ⌝ ⦄ := by
  mvcgen

/-!
## Pruning of trivial obligations

When `p_div = False` (resp. `p_fail = fun _ => False`), the generated
`step_spec` / `mvcgen_spec` lemmas should drop the corresponding
obligation rather than asking the user (or `mvcgen`) to discharge a
`¬ False` / `False → _` hypothesis.
-/

/-- `myDiv_spec_partial.step_spec` should require *only* `h_fail`
    (the `¬ False` divergence obligation must have been pruned). -/
example (x y : U32) (h_fail : ∀ (_ : Error), ¬ y.val = 0) :
    spec (myDiv x y) (fun z => z.val = x.val / y.val) :=
  myDiv_spec_partial.step_spec x y h_fail

/-- `myDiv_spec_partial.mvcgen_spec` should require *only* `h_ok`
    and `h_fail` (the `False → _` divergence obligation must have been
    pruned). -/
example (x y : U32)
    {Q : Std.Do.PostCond U32 (.except (ULift Error) (.except PUnit .pure))}
    (h_ok   : ∀ r, r.val = x.val / y.val → (Q.1 r).down)
    (h_fail : ∀ (e : Error), y.val = 0 → (Q.2.1 (.up e)).down) :
    ⦃ ⌜ True ⌝ ⦄ (myDiv x y) ⦃ Q ⦄ :=
  myDiv_spec_partial.mvcgen_spec x y h_ok h_fail

/-! Both failure and divergence are `False` — every obligation should disappear. -/

opaque myAlwaysOk (x : U32) : Result U32

@[step]
axiom myAlwaysOk_spec_partial (x : U32) :
  spec_partial (myAlwaysOk x)
    (fun z => z.val = x.val)
    (fun _ => False)
    False

/-- Step spec: no `h_fail`, no `h_div`. -/
example (x : U32) : spec (myAlwaysOk x) (fun z => z.val = x.val) :=
  myAlwaysOk_spec_partial.step_spec x

/-- Mvcgen spec: only `h_ok`. -/
example (x : U32)
    {Q : Std.Do.PostCond U32 (.except (ULift Error) (.except PUnit .pure))}
    (h_ok : ∀ r, r.val = x.val → (Q.1 r).down) :
    ⦃ ⌜ True ⌝ ⦄ (myAlwaysOk x) ⦃ Q ⦄ :=
  myAlwaysOk_spec_partial.mvcgen_spec x h_ok

/-! Non-trivial `p_div` — the obligation must be preserved. -/

opaque myMayLoop (x : U32) : Result U32

@[step]
axiom myMayLoop_spec_partial (x : U32) :
  spec_partial (myMayLoop x)
    (fun z => z.val = x.val)
    (fun _ => False)
    (x.val = 0)

/-- The `h_div` binder must still be present because `p_div = (x.val = 0)`
    is not trivially discharged. -/
example (x : U32) (h_div : ¬ x.val = 0) :
    spec (myMayLoop x) (fun z => z.val = x.val) :=
  myMayLoop_spec_partial.step_spec x h_div

/-! Universe polymorphism: a `spec_partial` lemma over a higher-universe
    `α` must still produce a well-typed `mvcgen_spec`. -/

opaque myId {α : Type u} (x : α) : Result α

@[step]
axiom myId_spec_partial {α : Type u} (x : α) :
  spec_partial (myId x) (fun z => z = x) (fun _ => False) False

example {α : Type u} (x : α) : spec (myId x) (fun z => z = x) :=
  myId_spec_partial.step_spec x

example {α : Type u} (x : α) :
    ⦃ ⌜ True ⌝ ⦄ (myId x) ⦃ ⇓ z => ⌜ z = x ⌝ ⦄ := by
  mvcgen

end Aeneas.Step.SpecPartialTests
