import Aeneas.Std.Scalar
import Aeneas.Std.Array
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result Std.Do

/-!
# Tests: mvcgen spec generation from @[step]

For every @[step] theorem `foo_spec`, the attribute handler also generates
`foo_spec.mvcgen_spec : Triple (f args) ⌜True⌝ post⟨fun r => ⌜Q r⌝, fun _ => ⌜False⌝⟩`.

Universe-polymorphic theorems are specialised to Type 0 (all concrete types).
-/

-- Scalar spec: generated at same universe
#check @UScalar.add_spec.mvcgen_spec
-- Expected: ∀ {ty} {x y : UScalar ty}, ↑x + ↑y ≤ UScalar.max ty → ⦃⌜True⌝⦄ (x + y) ⦃...⦄

-- Array spec: generated as Type-0 specialisation (α : Type, not α : Type u)
#check @Array.index_usize_spec.mvcgen_spec
-- Expected: ∀ {α : Type} (v : Array α) ..., ⦃⌜True⌝⦄ v[↑i]! ⦃...⦄

-- Scalar mvcgen_spec is usable as a direct term proof
example {ty} {x y : UScalar ty} (hmax : x.val + y.val ≤ UScalar.max ty) :
    ⦃⌜True⌝⦄ (x + y) ⦃post⟨fun z => ⌜(z.val : Nat) = x.val + y.val⌝, fun _ => ⌜False⌝⟩⦄ :=
  UScalar.add_spec.mvcgen_spec hmax
