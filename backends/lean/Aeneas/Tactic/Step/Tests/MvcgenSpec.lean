import Aeneas.Std.Scalar
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result Std.Do

/-!
# Tests: mvcgen spec generation from @[step]

For every @[step] theorem `foo_spec`, the attribute handler also generates
`foo_spec.mvcgen_spec : Triple (f args) ⌜True⌝ post⟨fun r => ⌜Q r⌝, fun _ => ⌜False⌝⟩`.
-/

-- The generated lemma should exist and have the correct Triple type
#check @UScalar.add_spec.mvcgen_spec

-- mvcgen should be able to use the generated @[spec] lemma directly
example {ty} {x y : UScalar ty} (hmax : x.val + y.val ≤ UScalar.max ty) :
    ⦃⌜True⌝⦄ (x + y) ⦃post⟨fun z => ⌜(z.val : Nat) = x.val + y.val⌝, fun _ => ⌜False⌝⟩⦄ :=
  UScalar.add_spec.mvcgen_spec hmax
