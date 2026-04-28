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

/-- Test: `step` can apply a partial-spec lemma against a success-only goal.
    After `step`, the user is left with the Result-level monotonicity goal
    and case-splits on the result (and on `Error` for the fail branch) to
    discharge each branch. -/
example (b : Bool) (hb : b = true) : succOrPanic b ⦃ x => x = 1 ⦄ := by
  step
  rcases x with _ | e | _ <;> [skip; cases e; skip] <;>
    simp_all [Std.WP.successPost]

/-- Test: explicitly invoke the partial-spec arithmetic lemma
    `UScalar.add_spec_partial` in leaf position. The user gets the partial
    post and case-splits to handle each branch. -/
example (x y : U32) (h : x.val + y.val ≤ U32.max) :
    x + y ⦃ z => z.val = x.val + y.val ⦄ := by
  step with UScalar.add_spec_partial
  rcases z with _ | e | _ <;> simp_all [Std.WP.successPost] <;> scalar_tac

/-- Test: same for subtraction. -/
example (x y : U32) (h : y.val ≤ x.val) :
    x - y ⦃ z => z.val = x.val - y.val ⦄ := by
  step with UScalar.sub_spec_partial
  rcases z with _ | e | _ <;> simp_all [Std.WP.successPost] <;> scalar_tac

/-- Test: same for multiplication. -/
example (x y : U32) (h : x.val * y.val ≤ U32.max) :
    x * y ⦃ z => z.val = x.val * y.val ⦄ := by
  step with UScalar.mul_spec_partial
  rcases z with _ | e | _ <;> simp_all [Std.WP.successPost] <;> scalar_tac

/-- Test: `step with X_spec_partial` fires in `let`-bind position. With
    `trySplitPartialBind` in `stepWith`, the fail / div obligations are
    automatically discharged when the input bounds imply success; only the
    ok-continuation remains and `step`'s normal `introOutputs` pipeline
    introduces the bound output and post-condition. The post is the
    partial-form ok-branch (a conjunction including the bound). -/
example (x y : U32) (h1 : x.val + y.val ≤ U32.max)
    (h2 : x.val + y.val + 1 ≤ U32.max) :
    (do let z ← x + y; z + 1#u32) ⦃ w => w.val = x.val + y.val + 1 ⦄ := by
  step with UScalar.add_spec_partial
  -- Only ok-continuation remains; `z` and `z_post` already introduced.
  step with UScalar.add_spec_partial
  rcases w with _ | e | _ <;> simp_all [Std.WP.successPost] <;> scalar_tac

/-- Test: `let* ⟨ z, h ⟩ ← X_spec_partial` works against partial-spec
    lemmas. The default fail/div discharge in `trySplitPartialBind` makes
    `let*` partial-aware: the ok-continuation is left as the main goal,
    `z` and `h` are introduced from the ok-continuation's `∀ z, P (ok z) →
    spec (k z) Q` shape. Note that `h` is a *conjunction* including the
    bound condition (`x.val + y.val ≤ U32.max ∧ z.val = ...`). -/
example (x y : U32) (h1 : x.val + y.val ≤ U32.max)
    (h2 : x.val + y.val + 1 ≤ U32.max) :
    (do let z ← x + y; z + 1#u32) ⦃ w => w.val = x.val + y.val + 1 ⦄ := by
  let* ⟨ z, hz ⟩ ← UScalar.add_spec_partial
  step with UScalar.add_spec_partial
  rcases w with _ | e | _ <;> simp_all [Std.WP.successPost] <;> scalar_tac

end partial_spec_tests
