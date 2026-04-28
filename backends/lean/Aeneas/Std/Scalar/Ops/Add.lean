import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Addition: Definitions
-/
def UScalar.add {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  UScalar.tryMk ty (x.val + y.val)

def IScalar.add {ty : IScalarTy} (x y : IScalar ty) : Result (IScalar ty) :=
  IScalar.tryMk ty (x.val + y.val)

def UScalar.try_add {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (add x y)

def IScalar.try_add {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (add x y)

instance {ty} : HAdd (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hAdd x y := UScalar.add x y

instance {ty} : HAdd (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hAdd x y := IScalar.add x y


/-!
# Addition: Theorems
-/

theorem UScalar.add_equiv {ty} (x y : UScalar ty) :
  x + y ⦃
    | ok z =>
      x.val + y.val < 2^ty.numBits ∧
      z.val = x.val + y.val ∧
      z.bv = x.bv + y.bv
    | fail _ => ¬ (UScalar.inBounds ty (x.val + y.val))
  ⦄ := by
  unfold Std.WP.spec
  have : x + y = add x y := by rfl
  rw [this]
  simp [add]
  have h := tryMk_eq ty (↑x + ↑y)
  simp [inBounds] at h
  split at h <;> simp_all
  zify; simp
  zify at h
  have := @Int.emod_eq_of_lt (x.val + y.val) (2^ty.numBits) (by omega) (by omega)
  simp [*]

theorem IScalar.add_equiv {ty} (x y : IScalar ty) :
  x + y ⦃
    | ok z =>
      IScalar.inBounds ty (x.val + y.val) ∧
      z.val = x.val + y.val ∧
      z.bv = x.bv + y.bv
    | fail _ => ¬ (IScalar.inBounds ty (x.val + y.val))
  ⦄ := by
  unfold Std.WP.spec
  have : x + y = add x y := by rfl
  rw [this]
  simp [add]
  have h := tryMk_eq ty (↑x + ↑y)
  simp [inBounds] at h
  split at h <;> simp_all
  apply BitVec.eq_of_toInt_eq
  simp
  have := bmod_pow_numBits_eq_of_lt ty (x.val + y.val) (by omega) (by omega)
  simp [*]

/-!
Theorems about the addition, with a specification which uses
integers and bit-vectors.
-/

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.add_bv_spec {ty} {x y : UScalar ty}
  (hmax : ↑x + ↑y ≤ UScalar.max ty) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ∧ z.bv = x.bv + y.bv ⦄ := by
  have h := @add_equiv ty x y
  simp only [Std.WP.spec] at h ⊢
  split at h <;> simp_all [max]
  have : 0 < 2^ty.numBits := by simp
  omega

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.add_bv_spec {ty}  {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x + ↑y)
  (hmax : ↑x + ↑y ≤ IScalar.max ty) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ∧ z.bv = x.bv + y.bv ⦄ := by
  have h := @add_equiv ty x y
  simp only [Std.WP.spec] at h ⊢
  split at h <;> simp_all [min, max]
  omega

uscalar theorem «%S».add_bv_spec {x y : «%S»} (hmax : x.val + y.val ≤ «%S».max) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ∧ z.bv = x.bv + y.bv ⦄ :=
  UScalar.add_bv_spec (by scalar_tac)

iscalar theorem «%S».add_bv_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ «%S».max) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ∧ z.bv = x.bv + y.bv ⦄ :=
  IScalar.add_bv_spec (by scalar_tac) (by scalar_tac)

/-!
Theorems about the addition, with a specification which uses
only integers. Those are the most common to use, so we mark them with the
`step` attribute.
-/

/-- Generic theorem - shouldn't be used much -/
@[step]
theorem UScalar.add_spec {ty} {x y : UScalar ty}
  (hmax : ↑x + ↑y ≤ UScalar.max ty) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ⦄ := by
  have h := @add_equiv ty x y
  simp only [Std.WP.spec] at h ⊢
  split at h <;> simp_all [max]
  have : 0 < 2^ty.numBits := by simp
  omega

/-- Generic theorem - shouldn't be used much -/
@[step]
theorem IScalar.add_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x + ↑y)
  (hmax : ↑x + ↑y ≤ IScalar.max ty) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ⦄ := by
  have h := @add_equiv ty x y
  simp only [Std.WP.spec] at h ⊢
  split at h <;> simp_all [min, max]
  omega

uscalar @[step] theorem «%S».add_spec {x y : «%S»} (hmax : x.val + y.val ≤ «%S».max) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ⦄ :=
  UScalar.add_spec (by scalar_tac)

iscalar @[step] theorem «%S».add_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ «%S».max) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ⦄ :=
  IScalar.add_spec (by scalar_tac) (by scalar_tac)

/-!
Partial-spec form: covers both the success branch (with the bound implied as
part of the postcondition) and the failure branch (overflow). Useful when the
caller wants to reason about both outcomes without committing up front to a
bound. **Not** tagged with `@[step]` — to avoid conflicting with the existing
success-only `add_spec` (and the `step?` regression tests that pin specific
lemma names), users invoke these explicitly via `step with add_spec_partial`.
-/

theorem UScalar.add_spec_partial {ty} (x y : UScalar ty) :
  x + y ⦃
    | ok z => x.val + y.val ≤ UScalar.max ty ∧ z.val = x.val + y.val
    | fail _ => UScalar.max ty < x.val + y.val
  ⦄ := by
  have h := @add_equiv ty x y
  simp only [Std.WP.spec, max, inBounds] at h ⊢
  have hpow : 0 < 2^ty.numBits := by simp
  split at h
  · obtain ⟨h1, h2, _⟩ := h
    exact ⟨by omega, h2⟩
  · omega
  · exact h.elim

theorem IScalar.add_spec_partial {ty} (x y : IScalar ty) :
  x + y ⦃
    | ok z =>
      IScalar.min ty ≤ x.val + y.val ∧ x.val + y.val ≤ IScalar.max ty ∧
      z.val = x.val + y.val
    | fail _ => ¬ (IScalar.min ty ≤ x.val + y.val ∧ x.val + y.val ≤ IScalar.max ty)
  ⦄ := by
  have h := @add_equiv ty x y
  simp only [Std.WP.spec] at h ⊢
  split at h <;> simp_all [min, max, inBounds] <;> omega

/- Per-type wrappers (e.g. `U32.add_spec_partial`) are intentionally omitted
   for now: the generic `UScalar.add_spec_partial` / `IScalar.add_spec_partial`
   lemmas tagged with `@[step]` are picked up by the `step` tactic via
   type-class resolution on `«%S»`. -/

end Aeneas.Std
