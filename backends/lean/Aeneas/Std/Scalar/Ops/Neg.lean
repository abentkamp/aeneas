import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab

/-!
# Negation: Definitions
-/

iscalar @[step_pure_def] def «%S».neg (x : «%S») : Result («%S») := tryMk (- x.toInt)

class ResultNeg (α : Type u) where
  neg : α → Result α

prefix:75  "-?" => ResultNeg.neg

iscalar instance : ResultNeg «%S» where neg x := «%S».neg x

end Aeneas.Std
