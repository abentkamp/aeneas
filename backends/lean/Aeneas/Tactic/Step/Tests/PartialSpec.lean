import Aeneas.Std.Scalar
import Aeneas.Std.Array
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result Std.Do
set_option mvcgen.warning false

/-!
# Tests: partial spec generation from @[step]

For a theorem whose body is a `match` on a `Result α` (a "partial spec"), the
`@[step]` attribute auto-generates two lemmas:
- `<thName>.step_spec`: a success-only spec usable by the `step` tactic.
- `<thName>.mvcgen_spec`: an mvcgen-style triple.
-/

namespace PartialSpecTest

/-- Sample partial spec for `U32.add`.

(The proof goes via the fact that `U32.add` only ever returns `.integerOverflow`,
which lets us refine the `_ => False` arm.) -/
@[step]
theorem add_spec_partial (x y : U32) :
    match (x + y) with
    | .ok z => z.val = x.val + y.val
    | .fail .integerOverflow => x.val + y.val > U32.max
    | _ => False := by
  show match (UScalar.add x y) with
       | .ok z => z.val = x.val + y.val
       | .fail .integerOverflow => x.val + y.val > U32.max
       | _ => False
  unfold UScalar.add UScalar.tryMk Result.ofOption
  have hopt := UScalar.tryMkOpt_eq UScalarTy.U32 (x.val + y.val)
  split at hopt <;> simp_all [UScalar.inBounds, U32.max] <;> scalar_tac

/-- The mvcgen lemma was generated and registered with `@[spec]`. -/
example {x y : U8} (hmax : x.val + y.val ≤ U8.max) :
    ⦃ ⌜ True ⌝ ⦄ (x + y) ⦃ ⇓ z => ⌜ z.val = x.val + y.val ⌝ ⦄ := by
  mvcgen; scalar_tac

-- Show the type of the auto-generated mvcgen lemma.
#check @add_spec_partial.mvcgen_spec

-- Show the type of the auto-generated step lemma.
#check @add_spec_partial.step_spec

end PartialSpecTest
