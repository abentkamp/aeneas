import Lean
open Lean

namespace Aeneas

-- This file defines the metadata describing a "spec statement" — a predicate wrapping a
-- monadic program and its postcondition — that the `step` tactic operates on.
--
-- There is a single such statement, `pspec`, whose `SpecInfo` instance is `Std.WP.pspecInfo`
-- (see WP.lean). `step` references that instance directly via `specStatementLookup`; there is
-- no registration command or environment extension.

structure LiftingInfo where
  from_statement : Name
  conversion_thm : Name
  conversion_thm_inferred_args : Nat

structure SpecInfo where
  spec_name : Lean.Name
  arity : Nat
  program_index : Nat -- index into the arguments of the Result value
  post_index : Nat

  mk_spec_mono : Name
  mk_spec_mono_skip_args : Nat -- number of arguments to be inferred, before Result and Post arguments
  mk_spec_bind : Name
  mk_spec_bind_skip_args : Nat

  uncurry_elim_tactics : Array Lean.Name
  qimp_elim_tactics : Array Lean.Name

  to_mvcgen: Option Name

  liftings : Array LiftingInfo
  deriving Inhabited

end Aeneas
