import Aeneas.Std
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result Error

namespace partial_spec_tests

/-! Tests for the partial-correctness `⦃ | ok ... | fail ... ⦄` spec syntax. -/

/-- Toy function that returns `0` on success, panics on `b = false`. -/
def succOrPanic (b : Bool) : Result Nat :=
  match b with
  | true => ok 1
  | false => fail .panic

@[step]
theorem succOrPanic_spec_partial (b : Bool) :
    succOrPanic b ⦃
      | ok n => n = 1 ∧ b = true
      | fail .panic => b = false
    ⦄ := by
  unfold succOrPanic
  unfold Std.WP.specMatch
  cases b <;> simp

/-- Test: the partial-spec lemma can be used as a proof term directly. -/
example (b : Bool) :
    succOrPanic b ⦃
      | ok n => n = 1 ∧ b = true
      | fail .panic => b = false
    ⦄ := succOrPanic_spec_partial b

/-- Test: the partial-spec lemma is registered with `@[step]` and `step`
    finds it for a goal of identical shape. After `step` applies the lemma,
    the residual `qimp` goal is trivially closed. -/
example (b : Bool) :
    succOrPanic b ⦃
      | ok n => n = 1 ∧ b = true
      | fail .panic => b = false
    ⦄ := by
  step
  assumption

end partial_spec_tests
