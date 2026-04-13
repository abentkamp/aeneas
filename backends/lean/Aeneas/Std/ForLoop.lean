/- ForIn instances for Aeneas iterators.

   These instances enable native Lean 4 `for x in xs do` syntax for
   Rust iterators that Aeneas handles. They are used when Aeneas is invoked
   with the `-lean-for-loops` flag. -/
import Aeneas.Std.Primitives
import Aeneas.Std.Core.Iter
import Aeneas.Std.SliceIter

namespace Aeneas.Std

open Result

/-- ForIn instance for Range Usize iterators in the Result monad.
    Enables `for i in (range : Range Usize) do body` in Aeneas-generated code. -/
instance : ForIn Result (core.ops.range.Range Usize) Usize where
  forIn range init f :=
    loop (fun p => do
      let (r, acc) := p
      let (opt, r') ← core.iter.range.IteratorRange.next core.iter.range.StepUsize r
      match opt with
      | none => ok (ControlFlow.done acc)
      | some i => do
        let step ← f i acc
        match step with
        | ForInStep.done acc' => ok (ControlFlow.done acc')
        | ForInStep.yield acc' => ok (ControlFlow.cont (r', acc')))
    (range, init)

/-- ForIn instance for slice iterators in the Result monad.
    Enables `for x in (iter : core.slice.iter.Iter T) do body`. -/
instance {T : Type} : ForIn Result (core.slice.iter.Iter T) T where
  forIn iter init f :=
    loop (fun p => do
      let (it, acc) := p
      let (opt, it') ← core.slice.iter.IteratorSliceIter.next it
      match opt with
      | none => ok (ControlFlow.done acc)
      | some x => do
        let step ← f x acc
        match step with
        | ForInStep.done acc' => ok (ControlFlow.done acc')
        | ForInStep.yield acc' => ok (ControlFlow.cont (it', acc')))
    (iter, init)

/-- ForIn instance for ChunksExact slice iterators in the Result monad.
    Enables `for chunk in data.chunks_exact(n) do body`. -/
instance {T : Type} : ForIn Result (core.slice.iter.ChunksExact T) (Slice T) where
  forIn iter init f :=
    loop (fun p => do
      let (it, acc) := p
      let (opt, it') ← core.slice.iter.IteratorChunksExact.next it
      match opt with
      | none => ok (ControlFlow.done acc)
      | some chunk => do
        let step ← f chunk acc
        match step with
        | ForInStep.done acc' => ok (ControlFlow.done acc')
        | ForInStep.yield acc' => ok (ControlFlow.cont (it', acc')))
    (iter, init)

end Aeneas.Std
