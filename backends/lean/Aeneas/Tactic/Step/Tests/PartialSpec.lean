import Aeneas.Std
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result Error

namespace partial_spec_tests

/-! Tests for the partial-correctness `⦃ | ok ... | fail ... ⦄` spec syntax,
    which now elaborates to the same `Std.WP.spec` constant as the
    success-only `⦃ x => P x ⦄` form. -/

/-- Toy function that returns `1` on success, panics on `b = false`. This
    function actually exhibits the failing branch when `b = false`. -/
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
  unfold Std.WP.spec
  cases b <;> simp

/-- Test: the partial-spec lemma can be used as a proof term directly. -/
example (b : Bool) :
    succOrPanic b ⦃
      | ok n => n = 1 ∧ b = true
      | fail .panic => b = false
    ⦄ := succOrPanic_spec_partial b

/-- Test: a call site where the failing branch actually fires. We pass `false`
    so `succOrPanic false = fail .panic`, then the partial-spec lemma lets us
    extract that the failure was specifically `panic`. -/
example : ∃ e, succOrPanic false = fail e ∧ e = .panic := by
  have h := succOrPanic_spec_partial false
  unfold Std.WP.spec at h
  unfold succOrPanic at *
  simp_all

/-- Test: a value-derived failure case. Show that for any input, if we pass
    `false`, the result is exactly `fail .panic`. -/
example : succOrPanic false = fail .panic := by
  have h := succOrPanic_spec_partial false
  unfold Std.WP.spec at h
  unfold succOrPanic at *
  simp_all

end partial_spec_tests
