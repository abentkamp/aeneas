import Aeneas.Std.Primitives
import Std.Do
import Aeneas.Tactic.Solver.Grind.Init

namespace Aeneas.Std.WP

open Std Result

def Post α := (α -> Prop)
def Pre := Prop

def Wp α := Post α → Pre

def wp_return (x:α) : Wp α := fun p => p x

def wp_bind (m:Wp α) (k:α -> Wp β) : Wp β :=
  fun p => m (fun r => k r p)

def wp_ord (wp1 wp2:Wp α) :=
  forall p, wp1 p → wp2 p

/-- The unified `spec` combinator: a postcondition is a predicate over the
    whole `Result α`, so it can constrain the `ok`, `fail`, and `div`
    branches separately.

    The two surface forms both elaborate to this:
    - `f ⦃ x => P x ⦄` (success-only) → `spec f (fun r => match r with | ok x => P x | _ => False)`
    - `f ⦃ | ok x => P x | fail e => Q e ⦄` (branch-by-branch) →
      `spec f (fun r => match r with | ok x => P x | fail e => Q e | _ => False)`
-/
def spec {α} (x : Result α) (p : Result α → Prop) : Prop := p x

/-- Lift a value-level postcondition (`α → Prop`) to a Result-level
    postcondition (`Result α → Prop`) by treating non-`ok` outcomes as
    forbidden (`False`). This is the canonical wrapping for the historical
    success-only spec syntax `f ⦃ x => P x ⦄`, which elaborates into
    `spec f (successPost (fun x => P x))`. -/
def successPost {α} (P : α → Prop) : Result α → Prop :=
  fun r => match r with | ok x => P x | _ => False

/-- A value-level postcondition `α → Prop` is automatically coerced to a
    Result-level postcondition `Result α → Prop` as `successPost P`. This
    lets callers continue to pass success-only predicates to `spec`. -/
instance {α} : Coe (α → Prop) (Result α → Prop) where
  coe P := successPost P

@[simp, grind =, agrind =]
theorem successPost_ok {α} (v : α) (P : α → Prop) :
  successPost P (ok v) ↔ P v := by simp [successPost]

@[simp, grind =, agrind =]
theorem successPost_fail {α} (e : Error) (P : α → Prop) :
  successPost P (fail e : Result α) ↔ False := by simp [successPost]

@[simp, grind =, agrind =]
theorem successPost_div {α} (P : α → Prop) :
  successPost P (Result.div : Result α) ↔ False := by simp [successPost]

/-- Auxiliary helper that we use to decompose tuples in post-conditions.

Example: `f 0 ⦃ x y z => ... ⦄` desugars to `spec (f 0) (predn fun x => predn fun y z => ...)`.

**Remark:** an alternative would be to parameterize `predn` with a list of types, e.g.:
```lean
def prednTy (tys : List α) : Type :=
  match tys with
  | [] => Prop
  | ty :: tys => ty → prednTy tys

def prodTy (tys : List α) : Type :=
  match tys with
  | [] => ()
  | [x] => x
  | ty :: tys => (ty, prodTy tys)

def predn {tys : List α} (p : prednTy tys) : prodTy tys → Prop
```
but there are two issues:
- this kind of dependent types is hard to work with
- it forces all the types to live in the same universe, which is especially cumbersome as we do not have
  universe cumulativity
-/
def predn {α β} (p : α → β → Prop) : α × β → Prop :=
  fun (x, y) => p x y

@[simp] theorem predn_pair x y (p : α → β → Prop) : predn p (x, y) = p x y := by simp [predn]
@[defeq] theorem predn_eq x (p : α → β → Prop) : predn p x = p x.fst x.snd := by simp [predn]

/-- Spec reduction on `ok`: stated specifically for the success-only post
    `successPost p`, so it directly recovers the historical `spec (ok x) p ↔
    p x` form for callers that simp on `spec_ok`. -/
@[simp, grind =, agrind =]
theorem spec_ok {α} (v : α) (p : α → Prop) :
  spec (ok v) (successPost p) ↔ p v := by simp [spec, successPost]

@[simp, grind =, agrind =]
theorem spec_fail {α} (e : Error) (p : α → Prop) :
  spec (fail e : Result α) (successPost p) ↔ False := by simp [spec, successPost]

@[simp, grind =, agrind =]
theorem spec_div {α} (p : α → Prop) :
  spec (Result.div : Result α) (successPost p) ↔ False := by simp [spec, successPost]

/-- Spec reduction on the general (Result-level) post: unfolds `spec` to its
    definitional form `p v`. Not registered as `@[simp]` to keep the `spec`
    head visible to the `step` tactic; users can fold/unfold by
    `simp only [spec_apply]` or directly `simp only [spec]`. -/
theorem spec_apply {α} (v : Result α) (p : Result α → Prop) :
  spec v p ↔ p v := by simp [spec]

/-- Monotonicity for the success-only spec form. -/
theorem spec_mono {α} {P₁ : α → Prop} {m : Result α} {P₀ : α → Prop}
  (h : spec m (successPost P₀)) (hmono : ∀ x, P₀ x → P₁ x) :
  spec m (successPost P₁) := by
  unfold spec successPost at *
  cases m <;> grind

/-- Bind for the success-only spec form. -/
theorem spec_bind {α β} {k : α → Result β} {Pₖ : β → Prop} {m : Result α} {Pₘ : α → Prop} :
  spec m (successPost Pₘ) →
  (∀ x, Pₘ x → spec (k x) (successPost Pₖ)) →
  spec (Std.bind m k) (successPost Pₖ) := by
  intro Hm Hk
  cases m
  · simp [spec, successPost] at *; apply Hk; exact Hm
  · simp [spec, successPost] at *
  · simp [spec, successPost] at *

/-- Monotonicity for the general (Result-level) spec form. -/
theorem spec_mono_g {α} {P₁ : Result α → Prop} {m : Result α} {P₀ : Result α → Prop}
  (h : spec m P₀) (hmono : ∀ r, P₀ r → P₁ r) : spec m P₁ := by
  unfold spec at *; apply hmono; exact h

/-- Bind for the general (Result-level) spec form. -/
theorem spec_bind_g {α β} {m : Result α} {k : α → Result β}
  {Pₘ : Result α → Prop} {Pₖ : Result β → Prop} :
  spec m Pₘ →
  (∀ x, Pₘ (ok x) → spec (k x) Pₖ) →
  (∀ e, Pₘ (fail e) → Pₖ (fail e)) →
  (Pₘ div → Pₖ div) →
  spec (Std.bind m k) Pₖ := by
  intro Hm Hok Hfail Hdiv
  cases m
  · simp [spec] at *; apply Hok; exact Hm
  · simp [spec] at *; apply Hfail; exact Hm
  · simp [spec] at *; apply Hdiv; exact Hm

/-- Small helper to currify functions -/
def curry {α β γ} (f : α × β → γ) (x : α) : β → γ := fun y => f (x, y)

/-- Implication -/
def imp (P Q : Prop) : Prop := P → Q

@[simp]
theorem imp_and_iff (P0 P1 Q : Prop) : imp (P0 ∧ P1) Q ↔ P0 → imp P1 Q := by simp [imp]

/-- Implication with quantifier. The carrier type is generic, so this works
    for both value-level postconditions (`α → Prop`) and Result-level
    postconditions (`Result α → Prop`). -/
def qimp {α} (P₀ P₁ : α → Prop) : Prop := ∀ x, P₀ x → P₁ x

/-- We use this lemma to decompose nested `predn` predicates into a sequence of universal quantifiers. -/
@[simp]
def qimp_predn {α₀ α₁} (P : α₀ → α₁ → Prop) (Q : α₀ × α₁ → Prop) :
  qimp (predn P) Q ↔ ∀ x, qimp (P x) (curry Q x) := by
  simp [qimp, curry]

/-- We use this lemma to eliminate `imp` after we decomposed the nested `predn` -/
theorem qimp_iff {α} (P₀ P₁ : α → Prop) : qimp P₀ P₁ ↔ ∀ x, imp (P₀ x) (P₁ x) := by simp [qimp, imp]

/-- Convert a partial-spec to a success-only spec by adding hypotheses that
    rule out the `fail` and `div` branches. Used by the `@[step]` attribute
    to synthesize a `_step` alias whose conclusion fits the existing
    success-only `step` pipeline, so the tactic itself does not need to
    handle partial posts. -/
theorem partial_to_success_with_hyps {α} {x : Result α}
    {P : Result α → Prop} {P_ok : α → Prop}
    (h : spec x P)
    (h_ok : ∀ z, P (.ok z) → P_ok z)
    (h_no_fail : ∀ e, ¬ P (.fail e))
    (h_no_div : ¬ P .div) :
    spec x (successPost P_ok) := by
  unfold spec successPost at *
  cases x
  case ok z => exact h_ok _ h
  case fail e => exact (h_no_fail _ h).elim
  case div => exact (h_no_div h).elim

/-- Companion to `spec_imp_exists` for partial-spec lemmas: given the partial
    spec plus hypotheses ruling out the fail/div branches, extract the value
    along with the ok-branch postcondition. -/
theorem partial_imp_exists {α} {m : Result α} {P : Result α → Prop}
    (h : spec m P)
    (h_no_fail : ∀ e, ¬ P (.fail e))
    (h_no_div : ¬ P .div) :
    ∃ v, m = ok v ∧ P (.ok v) := by
  unfold spec at h
  cases m
  case ok z => exact ⟨z, rfl, h⟩
  case fail e => exact (h_no_fail _ h).elim
  case div => exact (h_no_div h).elim

/-- Alternative to `spec_mono` (success-only): introduces a `qimp` between the
    inner value-level postconditions. -/
theorem spec_mono' {α} {P₁ : α → Prop} {m : Result α} {P₀ : α → Prop}
  (h : spec m (successPost P₀)) : qimp P₀ P₁ → spec m (successPost P₁) := by
  intro HMonPost
  unfold spec successPost at *
  cases m <;> grind [qimp]

/-- Implication of a `spec` predicate with quantifier (value-level form). -/
def qimp_spec {α β} (P : α → Prop) (k : α → Result β) (Q : β → Prop) : Prop :=
  ∀ x, P x → spec (k x) (successPost Q)

/-- This alternative to `spec_bind` controls the introduction of universal
    quantifiers with `imp_spec` (success-only). -/
theorem spec_bind' {α β} {k : α → Result β} {Pₖ : β → Prop}
  {m : Result α} {Pₘ : α → Prop} :
  spec m (successPost Pₘ) →
  qimp_spec Pₘ k Pₖ →
  spec (Std.bind m k) (successPost Pₖ) := by
  intro Hm Hk
  cases m
  · simp [spec, successPost] at *; apply Hk; exact Hm
  · simp [spec, successPost] at *
  · simp [spec, successPost] at *

/-- We use this lemma to decompose nested `predn` predicates into a sequence
    of universal quantifiers. -/
@[simp]
def qimp_spec_predn {α₀ α₁ β} (P : α₀ → α₁ → Prop) (k : α₀ × α₁ → Result β) (Q : β → Prop) :
  qimp_spec (predn P) k Q ↔ ∀ x, qimp_spec (P x) (curry k x) Q := by
  simp [qimp_spec, curry]

/-- We use this lemma to eliminate `imp_spec` after we decomposed the nested `predn` -/
def qimp_spec_iff {α β} (P : α → Prop) (k : α → Result β) (Q : β → Prop) :
  qimp_spec P k Q ↔ ∀ x, imp (P x) (spec (k x) (successPost Q)) := by
  simp [qimp_spec, imp]

@[simp]
theorem qimp_exists {α β} (P₀ : β → α → Prop) (P₁ : α → Prop) :
  qimp (fun x => ∃ y, P₀ y x) P₁ ↔ ∀ x, qimp (P₀ x) P₁ := by
  simp only [qimp, forall_exists_index]; grind

@[simp]
theorem qimp_spec_exists {α β γ} (P : γ → α → Prop) (k : α → Result β) (Q : β → Prop) :
  qimp_spec (fun x => ∃ y, P y x) k Q ↔ ∀ x, qimp_spec (P x) k Q := by
  simp only [qimp_spec, forall_exists_index]; grind

/-- For the success-only spec form, `spec m (successPost P)` is equivalent to
    "m succeeds and the value satisfies P". This recovers the historical
    `∃ y, m = ok y ∧ ...` reading. -/
theorem spec_equiv_exists {α} (m : Result α) (P : α → Prop) :
  spec m (successPost P) ↔ (∃ y, m = ok y ∧ P y) := by
  cases m <;> simp [spec, successPost]

theorem spec_imp_exists {α} {m : Result α} {P : α → Prop} :
  spec m (successPost P) → (∃ y, m = ok y ∧ P y) := by
  exact (spec_equiv_exists m P).1

theorem exists_imp_spec {α} {m : Result α} {P : α → Prop} :
  (∃ y, m = ok y ∧ P y) → spec m (successPost P) := by
  exact (spec_equiv_exists m P).2

end Aeneas.Std.WP

/-
We want the notations to live in the namespace `Aeneas`, not `Aeneas.Std.WP`
TODO: use https://github.com/leanprover/lean4/pull/11355
-/
namespace Aeneas

open Std WP Result

/-!
# Hoare triple notation and elaboration
-/

/- We use a priority of 55 for the inner term, which is exactly the priority for `|||`.
This way we can expressions like: `x + y ⦃ z => ... ⦄` without having to put parentheses around `x + y`. -/
scoped syntax:54 (name := specBoundTriple) term:55 " ⦃ " term+ " => " term " ⦄" : term
scoped syntax:54 (name := specPredTriple) term:55 " ⦃ " term " ⦄" : term

/-- Single alternative in the pattern-match form `⦃ | pat => post | ... ⦄`. -/
declare_syntax_cat specMatchAlt

scoped syntax (name := specMatchAltStx) "| " term " => " term : specMatchAlt

/-- Pattern-match form: lets the user specify what happens on `ok`, `fail` and
    `div` branches. The leading `|` after `⦃` distinguishes this from the other
    forms. Unmentioned branches default to `False` (forbidden); use
    `| _ => True` to leave a branch unconstrained. -/
scoped syntax:54 (name := specMatchTriple) term:55 " ⦃ " specMatchAlt+ " ⦄" : term

open Lean PrettyPrinter

/-- Macro expansion for the success-only form `e ⦃ x => p ⦄`: wraps the
    predicate in `successPost`, which forbids `fail`/`div`. -/
macro_rules (kind := specBoundTriple)
  | `($e ⦃ $x => $p ⦄) => do
    `(_root_.Aeneas.Std.WP.spec $e (_root_.Aeneas.Std.WP.successPost (fun $x => $p)))

/-- Macro expansion for the multi-binder form `e ⦃ x y z => p ⦄`: same as
    above, with `predn` decomposing the tuple value inside `ok`. -/
macro_rules (kind := specBoundTriple)
  | `($e ⦃ $x $xs:term* => $p ⦄) => do
    let mut xs : List (TSyntax `term) := x :: xs.toList
    let rec run (xs : List (TSyntax `term)) : MacroM (TSyntax `term) := do
      match xs with
      | [] => `($p)
      | [x] => `(fun $x => $p)
      | x :: xs =>
        let xs ← run xs
        `(_root_.Aeneas.Std.WP.predn fun $x => $xs)
    let post ← run xs
    `(_root_.Aeneas.Std.WP.spec $e (_root_.Aeneas.Std.WP.successPost $post))

/-- Macro expansion for the bare-predicate form `e ⦃ p ⦄`: the predicate is
    a value-level `α → Prop`, wrapped via `successPost`. -/
macro_rules (kind := specPredTriple)
  | `($e ⦃ $p ⦄) => do
    `(_root_.Aeneas.Std.WP.spec $e (_root_.Aeneas.Std.WP.successPost $p))

/-- Macro expansion for the pattern-match form. Unmentioned branches default to
    `False` (forbidden) via the appended catch-all `| _ => False` (skipped if
    the user already wrote a wildcard arm `| _ => ...`, to avoid redundancy). -/
macro_rules (kind := specMatchTriple)
  | `($e ⦃ $alts:specMatchAlt* ⦄) => do
    let arms : Array (TSyntax ``Lean.Parser.Term.matchAlt) ← alts.mapM fun alt =>
      match alt with
      | `(specMatchAlt| | $pat:term => $rhs:term) =>
          `(Lean.Parser.Term.matchAltExpr| | $pat => $rhs) <&> fun s => ⟨s.raw⟩
      | _ => Macro.throwUnsupported
    -- Detect whether the user already provided a wildcard `_` pattern. If so,
    -- skip the auto-appended `| _ => False` so Lean doesn't warn about a
    -- redundant arm.
    let userHasWildcard ← alts.anyM fun alt => do
      match alt with
      | `(specMatchAlt| | $pat:term => $_) =>
          match pat with
          | `(_) => pure true
          | _ => pure false
      | _ => pure false
    let arms ← if userHasWildcard then pure arms else do
      let defaultArm : TSyntax ``Lean.Parser.Term.matchAlt ←
        `(Lean.Parser.Term.matchAltExpr| | _ => False) <&> fun s => ⟨s.raw⟩
      pure (arms.push defaultArm)
    `(_root_.Aeneas.Std.WP.spec $e
        (fun __r => match __r with $arms:matchAlt*))

/-!
# Pretty-printing
-/

open Delaborator SubExpr

/--
Small helper to decompose nested `predn`s: we strip all the variables bound in a lambda inside the `predn`s.
-/
partial def telescopePredn (vars : Array SubExpr) (e : SubExpr) (k : Array SubExpr → SubExpr → Delab) : Delab :=
  e.expr.consumeMData.withApp fun app args => do
  if h: app.isConstOf ``predn ∧ args.size = 3 then
    let pred := args[2]
    Meta.lambdaTelescope pred.consumeMData fun args body => do
    let pos := e.pos.push 1
    if h: args.size = 1 ∧ body.isAppOf ``predn then
      let vars := vars.push { expr := args[0], pos := pos.push 0 }
      telescopePredn vars { expr := body, pos := pos.push 1} k
    else
      let mut vars := vars
      let mut pos := e.pos
      for arg in args do
        vars := vars.push { expr := arg, pos := pos.push 0 }
        pos := pos.push 1
      k vars { expr := body, pos }
  else do
    Meta.lambdaTelescope e.expr.consumeMData fun args body => do
    let mut vars := vars
    let mut pos := e.pos
    for arg in args do
      vars := vars.push { expr := arg, pos := pos.push 0 }
      pos := pos.push 1
    k vars { expr := body, pos }

def elabSubExpr (e : SubExpr) : Delab := withTheReader SubExpr (fun _ => e) delab

/-- Delaborator for the unified `spec`. Reverses the macro expansion:

    - If the post is `successPost f` (the canonical success-only form),
      decompose any nested `predn` and emit the historical form
      `e ⦃ x => P x ⦄` or `e ⦃ x y z => P x y z ⦄`.
    - Otherwise (branch-by-branch form), emit `e ⦃ | ok x => P x | ... ⦄`,
      stripping the macro's trailing `| _ => False` catch-all.

    Falls back to default printing if no shape matches. -/
@[scoped delab app.Aeneas.Std.WP.spec]
def delabSpec : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``spec 3
  let pos ← getPos
  let monadExpr ← elabSubExpr { expr := e.getAppArgs[1]!, pos := (pos.push 0).push 1 }
  let postExpr := e.getAppArgs[2]!
  -- Handle the success-only form: post = `successPost f`.
  if postExpr.consumeMData.isAppOfArity ``successPost 2 then
    let postArgs := postExpr.consumeMData.getAppArgs
    let fSub : SubExpr := { expr := postArgs[1]!, pos := (pos.push 1).push 1 }
    telescopePredn #[] fSub fun vars body => do
      let vars ← vars.mapM elabSubExpr
      let body ← elabSubExpr body
      if vars.size = 0 then
        `($monadExpr ⦃ $body:term ⦄)
      else
        let var := vars[0]!
        let vars := vars.drop 1
        `($monadExpr ⦃ $var $vars* => $body ⦄)
  else
    -- Branch-by-branch form: post = `fun r => match r with | ... | _ => False`.
    let body ← withNaryArg 2 delab
    let alts ← extractMatchAlts body
    let alts := stripFalseCatchall alts
    guard !alts.isEmpty
    let specAlts ← alts.mapM altToSpecAlt
    `($monadExpr ⦃ $specAlts:specMatchAlt* ⦄)
where
  extractMatchAlts (stx : Term) : DelabM (Array (TSyntax ``Lean.Parser.Term.matchAlt)) := do
    match stx with
    | `(fun $_ : $_ => match $scrut:term with $alts:matchAlt*) =>
        if scrut.raw.isIdent then pure alts else failure
    | `(fun $_ => match $scrut:term with $alts:matchAlt*) =>
        if scrut.raw.isIdent then pure alts else failure
    | `(fun $alts:matchAlt*) => pure alts
    | _ => failure
  stripFalseCatchall (alts : Array (TSyntax ``Lean.Parser.Term.matchAlt)) :
      Array (TSyntax ``Lean.Parser.Term.matchAlt) :=
    if alts.size > 0 then
      match alts[alts.size - 1]! with
      | `(Lean.Parser.Term.matchAltExpr| | _ => False) => alts.pop
      | _ => alts
    else alts
  altToSpecAlt (alt : TSyntax ``Lean.Parser.Term.matchAlt) :
      DelabM (TSyntax `specMatchAlt) := do
    match alt with
    | `(Lean.Parser.Term.matchAltExpr| | $pat:term => $rhs:term) =>
        `(specMatchAlt| | $pat => $rhs)
    | _ => failure

/-!
# Tests
-/

example : ok 0 ⦃ r => r = 0 ⦄ := by simp
example : spec (ok 0) (fun r => match r with | .ok x => x = 0 | _ => False) := by simp [spec]
example : ok 0 ⦃ _ => True ⦄ := by simp
example : spec (ok (0, 1)) (fun r => match r with | .ok (x, y) => x = 0 ∧ y = 1 | _ => False) := by simp [spec]
example : ok (0, 1) ⦃ (x, y) => x = 0 ∧ y = 1 ⦄ := by simp
example : ok (0, 1) ⦃ x y => x = 0 ∧ y = 1 ⦄ := by simp
example : ok (0, 1, 2) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = 2 ⦄ := by simp
example : ok (0, 1, true) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = true ⦄ := by simp
example : let P (x : Nat) := x = 0; ok 0 ⦃ P ⦄ := by simp

/-! Tests for the pattern-match form `⦃ | ok ... | fail ... ⦄`. -/

example : ok 0 ⦃ | ok r => r = 0 ⦄ := by simp [spec]
example : (ok 0 : Result Nat) ⦃ | ok r => r = 0 | fail _ => True ⦄ := by simp [spec]
example : (fail .integerOverflow : Result Nat)
    ⦃ | fail .integerOverflow => True ⦄ := by simp [spec]
example : (fail .integerOverflow : Result Nat)
    ⦃ | ok _ => False | fail .integerOverflow => True | _ => False ⦄ := by simp [spec]
-- The default `| _ => False` makes unmentioned cases impossible:
example : ¬ ((fail .panic : Result Nat) ⦃ | ok _ => True ⦄) := by simp [spec]
example : ¬ ((Result.div : Result Nat) ⦃ | ok _ => True ⦄) := by simp [spec]
-- Use `| _ => True` to leave a branch unconstrained.
example : (fail .panic : Result Nat) ⦃ | ok _ => False | _ => True ⦄ := by simp [spec]

end Aeneas

namespace Aeneas.Std.WP

section
  variable (U32 : Type) [HAdd U32 U32 (Result U32)]
  variable (x y : U32)

  #elab x + y ⦃ _ => True ⦄
  #elab True → x + y ⦃ _ => True ⦄
  #elab True ∧ x + y ⦃ _ => True ⦄

  -- Checking what happpens if we put post-conditions inside post-conditions
  example (f : Nat → Result (Nat × (Nat → Result Nat)))
          (_ : ∀ x, f x ⦃ (y, g) => y > 0 ∧ ∀ x, g x ⦃ z => z > y ⦄ ⦄ ∧ True)
   : True := by simp only
end

def add1 (x : Nat) := Result.ok (x + 1)
theorem  add1_spec (x : Nat) : add1 x ⦃ y => y = x + 1⦄ :=
  by simp [add1]

def add2 (x : Nat) := Result.ok (x + 1, x + 2)

theorem  add2_spec (x : Nat) : add2 x ⦃ (y, z) => y = x + 1 ∧ z = x + 2⦄ :=
  by simp [add2]

theorem  add2_spec' (x : Nat) : add2 x ⦃ y z => y = x + 1 ∧ z = x + 2⦄ :=
  by simp [add2]

private theorem massert_spec' (b : Prop) [Decidable b] (h : b) :
  massert b ⦃ _ => True ⦄ := by
  grind [massert]

@[simp]
theorem qimp_spec_unit {α} (P : Unit → Prop) (k : Unit → Result α) (Q : α → Prop) :
  qimp_spec P k Q ↔ (P () → k () ⦃ Q ⦄) := by
  grind [qimp_spec]

@[simp]
theorem qimp_unit (P Q : Unit → Prop) :
  qimp P Q ↔ (P () → Q ()) := by
  grind [qimp]

end Aeneas.Std.WP

namespace Aeneas.Std.WP

/-!
# mvcgen
-/

open Std Result
open Std.Do

instance Result.instWP : WP Result (.except Error (.except PUnit .pure)) where
  wp x := {
    apply Q := match x with | .ok a => Q.1 a | .fail e => Q.2.1 e | .div => Q.2.2.1 ()
    conjunctive Q₁ Q₂ := by
      apply SPred.bientails.of_eq
      cases x <;> simp
  }

instance : LawfulMonad Result where
    map_const := by intros; rfl
    id_map := by intros _ x; cases x <;> rfl
    seqLeft_eq := by intros _ _ x y; cases x <;> cases y <;> rfl
    seqRight_eq := by intros _ _ x y; cases x <;> cases y <;> rfl
    pure_seq := by intros _ _ _ x; cases x <;> rfl
    pure_bind := by intros; rfl
    bind_pure_comp := by intros; rfl
    bind_map := by intros; rfl
    bind_assoc := by intros _ _ _ x _ _; cases x <;> rfl

instance Result.instWPMonad : WPMonad Result (.except Error (.except PUnit .pure)) where
  wp_pure a := by ext; simp [wp]
  wp_bind x f := by ext Q; cases x <;> simp [wp]

theorem Result.of_wp {α} {x : Result α} (P : Result α → Prop) :
    (⊢ₛ wp⟦x⟧ post⟨fun a => ⌜P (.ok a)⌝,
                  fun e => ⌜P (.fail e)⌝,
                  fun () => ⌜P .div⌝⟩) → P x := by
  intro hspec
  simp only [instWP] at hspec
  split at hspec <;> simp_all

/-- Lift a success-only Aeneas spec to an mvcgen-compatible `Triple` with a
    value-level post. -/
theorem spec_to_mvcgen {α : Type} {x : Result α} {Q : α → Prop}
    (h : spec x (successPost Q)) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ Q r ⌝ ⦄ := by
  obtain ⟨v, hx, hQv⟩ := spec_imp_exists h
  subst hx
  simp [Triple, Result.instWP, hQv]

/-- Lift a general (Result-level) Aeneas spec to an mvcgen-compatible `Triple`
    with a 3-branch post characterizing all of `ok`, `fail`, `div`. -/
theorem spec_to_mvcgen_partial {α : Type} {x : Result α} {P : Result α → Prop}
    (h : spec x P) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ post⟨fun z => ⌜ P (.ok z) ⌝,
                          fun e => ⌜ P (.fail e) ⌝,
                          fun () => ⌜ P .div ⌝⟩ ⦄ := by
  unfold spec at h
  simp only [Triple, Result.instWP]
  cases x <;> simp_all

end Aeneas.Std.WP

namespace Aeneas.Std

/-!
# Loops
-/

/-- General spec for loops with a termination measure.

It is meant to derive lemmas to reason about loops: in most situations, one shouldn't
have to use it directly when verifying programs.
-/
theorem loop.spec {α : Type u} {β : Type v} {γ : Type w}
  (measure : α → γ)
  [wf : WellFoundedRelation γ]
  (inv : α → Prop)
  (post : β → Prop)
  (body : α → Result (ControlFlow α β)) (x : α)
  (hBody :
    ∀ x, inv x → body x ⦃ r =>
      match r with
      | .done y => post y
      | .cont x' => inv x' ∧ wf.rel (measure x') (measure x) ⦄)
  (hInv : inv x) :
  loop body x ⦃ post ⦄ := by
  suffices ∀ x' x, measure x = x' → inv x → loop body x ⦃ post ⦄
    by apply this <;> first | rfl | assumption
  apply @wf.wf.fix γ (fun x' =>
    ∀ x, measure x = x' →
    inv x → loop body x ⦃ post ⦄)
  grind [loop]

theorem loop.spec_decr_nat {α : Type u} {β : Type v}
  (measure : α → Nat)
  (inv : α → Prop)
  (post : β → Prop)
  (body : α → Result (ControlFlow α β)) (x : α)
  (hBody :
    ∀ x, inv x → body x ⦃ r =>
      match r with
      | .done y => post y
      | .cont x' => inv x' ∧ measure x' < measure x ⦄)
  (hInv : inv x) :
  loop body x ⦃ post ⦄ := by
  have := loop.spec measure inv post body x hBody hInv
  apply this

end Aeneas.Std
