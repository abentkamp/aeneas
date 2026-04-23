import Lean

namespace Aeneas.Std.ScalarElab

open Lean Elab Command Term Meta


initialize registerTraceClass `ScalarElabSubst
initialize registerTraceClass `ScalarElab

/-!

# Generic Scalar Definitions/Theorems
The following defines elaborators to factor out scalar definitions and theorems.
We do this because we often need to write a lot of very similar definitions for
all the scalars kinds. For instance:

```
theorem U8.add_toBitVec_spec {x y : U8} (hmax : x.toNat + y.toNat ≤ U8.max) :
  ∃ z, x + y = ok z ∧ (↑z : Nat) = ↑x + ↑y ∧ z.toBitVec = x.toBitVec + y.toBitVec :=
  UScalar.add_toBitVec_spec (by scalar_tac)

theorem U16.add_toBitVec_spec {x y : U16} (hmax : x.toNat + y.toNat ≤ U16.max) :
  ∃ z, x + y = ok z ∧ (↑z : Nat) = ↑x + ↑y ∧ z.toBitVec = x.toBitVec + y.toBitVec :=
  UScalar.add_toBitVec_spec (by scalar_tac)

... -- etc.
```

Instead, we want to write something like this:
```
uscalar theorem «%S».add_bv_spec {x y : «%S»} (hmax : x.toNat + y.toNat ≤ «%S».max) :
  ∃ z, x + y = ok z ∧ (↑z : Nat) = ↑x + ↑y ∧ z.toBitVec = x.toBitVec + y.toBitVec :=
  UScalar.add_toBitVec_spec (by scalar_tac)
```

and have all the theorems generated at once.

The way we make it work is extremely simple: we simply define a syntax `uscalar command`
which triggers an elaboration by which, for each scalar type, we recursively explore the
syntax of the command, and generate a command where we replaced all the name segments "%S"
with either "U8", or "U16", etc.

# Keywords
- `«%S»`: identifier to be replaced with a scalar name (e.g., `U8`, `U16`, etc.)
- `'S`: string to be replaced with a scalar name (e.g., `Clone'S ~> CloneU8`, etc.)
- `%BitWidth`: term to be replaced with a scalar bitwidth (e.g., `8`, `16`, ..., `System.Platform.numBits`)
- `%Size`: term to be replaced with a size (in bytes)

-/

def isSubstring (sub str : List Char) : Option (List Char) :=
  match sub, str with
  | [], _ => some str
  | hd :: sub, hd' :: str =>
    if hd == hd' then isSubstring sub str
    else none
  | _, _ => none

partial def elabString (ty : String) (str : String) : String :=
  let rec replace (str : List Char) : List Char :=
    match isSubstring "'S".toList str with
    | some str => ty.toList ++ replace str
    | none =>
      match str with
      | [] => []
      | c :: str => c :: replace str
  String.ofList (replace str.toList)

def elabSpecialName (ty : String) (n : Name) : CommandElabM Name := do
  trace[ScalarElabSubst] "elabSpecialName: {n}"
  match n with
  | .anonymous => pure .anonymous
  | .str pre str =>
    trace[ScalarElabSubst] "elabSpecialName: str case: {str}"
    let str := if str == "%S" then ty else elabString ty str
    pure (.str (← elabSpecialName ty pre) str)
  | .num pre i => pure (.num (← elabSpecialName ty pre) i)

partial def elabSpecial (ty : String) (bw size : Syntax) (stx : Syntax) : CommandElabM Syntax := do
  trace[ScalarElabSubst] "elabSpecial: stx: {stx}"
  match stx with
  | .missing => pure .missing
  -- Special case for %BitWidth
  | .node _ _ #[.atom _ "%BitWidth"] =>
    pure bw
  | .node _ _ #[.atom _ "%Size"] =>
    pure size
  | .node info kind args =>
    trace[ScalarElabSubst] "elabSpecial: node: {stx}"
    let args ← args.mapM (elabSpecial ty bw size)
    pure (.node info kind args)
  | .atom info val =>
    trace[ScalarElabSubst] "elabSpecial: atom: {val}"
    if val == "%BitWidth" then
      trace[ScalarElabSubst] "elabSpecial: replaced `%BitWidth`"
      pure bw
    else pure (.atom info val)
  | .ident info rawVal val preresolved =>
    trace[ScalarElabSubst] "elabSpecial: ident: {stx}"
    let val ← elabSpecialName ty val
    pure (.ident info rawVal val preresolved)

def elabCommand (tysBws : List (String × Syntax × Syntax)) (cmd : TSyntax `command) : CommandElabM Unit := do
  let elabOne (tyBw : String × Syntax × Syntax) : CommandElabM Unit := do
    let (ty, bw, size) := tyBw
    let cmd ← elabSpecial ty bw size cmd
    trace[ScalarElab] "Final declaration for {ty}:\n{cmd}"
    let cmd ← try liftMacroM (expandNamespacedDeclaration cmd) catch _ => pure cmd
    Command.elabCommand cmd
  for tyBw in tysBws do
    elabOne tyBw

scoped syntax "%BitWidth" : term
scoped syntax "%Size" : term
scoped syntax "%BitWidth1" : term
scoped syntax "%BitWidth2" : term
scoped syntax "%Size1" : term
scoped syntax "%Size2" : term

scoped syntax (name := uscalarCommand) "uscalar" command : command

@[command_elab uscalarCommand]
def uscalarCommandImpl : CommandElab := fun stx => do
  trace[ScalarElab] "uscalar_command (stx): {stx}"
  match stx with
  | `(uscalarCommand| uscalar $cmd) =>
    elabCommand [("U8", ←`(8), ←`(1)), ("U16", ←`(16), ←`(2)), ("U32", ←`(32), ←`(4)),
                 ("U64", ←`(64), ←`(8)), ("U128", ←`(128), ←`(16)),
                 ("Usize", ←`(System.Platform.numBits), ←`(System.Platform.numBits/8))] cmd
  | _ => throwUnsupportedSyntax

scoped syntax (name := uscalarNoUsizeCommand) "uscalar_no_usize" command : command

@[command_elab uscalarNoUsizeCommand]
def uscalarNoUsizeCommandImpl : CommandElab := fun stx => do
  trace[ScalarElab] "uscalar_no_usize_command (stx): {stx}"
  match stx with
  | `(uscalarNoUsizeCommand| uscalar_no_usize $cmd) =>
    elabCommand [("U8", ←`(8), ←`(1)), ("U16", ←`(16), ←`(2)), ("U32", ←`(32), ←`(4)),
                 ("U64", ←`(64), ←`(8)), ("U128", ←`(128), ←`(16))] cmd
  | _ => throwUnsupportedSyntax

scoped syntax (name := iscalarCommand) "iscalar" command : command

@[command_elab iscalarCommand]
def iscalarCommandImpl : CommandElab := fun stx => do
  trace[ScalarElab] "iscalar_command (stx): {stx}"
  match stx with
  | `(iscalarCommand| iscalar $cmd) =>
    elabCommand [("I8", ←`(8), ←`(1)), ("I16", ←`(16), ←`(2)), ("I32", ←`(32), ←`(4)),
                 ("I64", ←`(64), ←`(8)), ("I128", ←`(128), ←`(16)),
                 ("Isize", ←`(System.Platform.numBits), ←`(System.Platform.numBits/8))] cmd
  | _ => throwUnsupportedSyntax

scoped syntax (name := iscalarNoIsizeCommand) "iscalar_no_isize" command : command

@[command_elab iscalarNoIsizeCommand]
def iscalarNoIsizeNoIsizeCommandImpl : CommandElab := fun stx => do
  trace[ScalarElab] "iscalar_no_usize_command (stx): {stx}"
  match stx with
  | `(iscalarNoIsizeCommand| iscalar_no_isize $cmd) =>
    elabCommand [("I8", ←`(8), ←`(1)), ("I16", ←`(16), ←`(2)), ("I32", ←`(32), ←`(4)),
                 ("I64", ←`(64), ←`(8)), ("I128", ←`(128), ←`(16))] cmd
  | _ => throwUnsupportedSyntax

scoped syntax (name := scalarCommand) "scalar" command : command

@[command_elab scalarCommand]
def scalarCommandImpl : CommandElab := fun stx => do
  trace[ScalarElab] "scalar_command (stx): {stx}"
  match stx with
  | `(scalarCommand| scalar $cmd) =>
    elabCommand [("U8", ←`(8), ←`(1)), ("U16", ←`(16), ←`(2)), ("U32", ←`(32), ←`(4)),
                 ("U64", ←`(64), ←`(8)), ("U128", ←`(128), ←`(16)),
                 ("Usize", ←`(System.Platform.numBits), ←`(System.Platform.numBits/8)),
                 ("I8", ←`(8), ←`(1)), ("I16", ←`(16), ←`(2)), ("I32", ←`(32), ←`(4)),
                 ("I64", ←`(64), ←`(8)), ("I128", ←`(128), ←`(16)),
                 ("Isize", ←`(System.Platform.numBits), ←`(System.Platform.numBits/8))] cmd
  | _ => throwUnsupportedSyntax

/-!
# Two-Scalar Elaborators

The following extends the scalar elaboration scheme to support two scalar type
placeholders simultaneously:

- `«%S1»` / `'S1` / `%BitWidth1` / `%Size1` — first scalar type
- `«%S2»` / `'S2` / `%BitWidth2` / `%Size2` — second scalar type

Four commands are provided:

| Command    | S1 list     | S2 list    |
|------------|-------------|------------|
| `uuscalar` | unsigned    | unsigned   |
| `uiscalar` | unsigned    | signed     |
| `iuscalar` | signed      | unsigned   |
| `iiscalar` | signed      | signed     |
-/

partial def elabString2 (ty1 ty2 : String) (str : String) : String :=
  -- Replace 'S2 before 'S1 so the longer token is matched first
  let rec replace (str : List Char) : List Char :=
    match isSubstring "'S2".toList str with
    | some rest => ty2.toList ++ replace rest
    | none =>
      match isSubstring "'S1".toList str with
      | some rest => ty1.toList ++ replace rest
      | none =>
        match str with
        | [] => []
        | c :: rest => c :: replace rest
  String.ofList (replace str.toList)

def elabSpecialName2 (ty1 ty2 : String) (n : Name) : CommandElabM Name := do
  trace[ScalarElabSubst] "elabSpecialName2: {n}"
  match n with
  | .anonymous => pure .anonymous
  | .str pre str =>
    let str :=
      if str == "%S1" then ty1
      else if str == "%S2" then ty2
      else elabString2 ty1 ty2 str
    pure (.str (← elabSpecialName2 ty1 ty2 pre) str)
  | .num pre i => pure (.num (← elabSpecialName2 ty1 ty2 pre) i)

partial def elabSpecial2 (ty1 ty2 : String) (bw1 size1 bw2 size2 : Syntax)
    (stx : Syntax) : CommandElabM Syntax := do
  trace[ScalarElabSubst] "elabSpecial2: stx: {stx}"
  match stx with
  | .missing => pure .missing
  | .node _ _ #[.atom _ "%BitWidth1"] => pure bw1
  | .node _ _ #[.atom _ "%BitWidth2"] => pure bw2
  | .node _ _ #[.atom _ "%Size1"]     => pure size1
  | .node _ _ #[.atom _ "%Size2"]     => pure size2
  | .node info kind args =>
    let args ← args.mapM (elabSpecial2 ty1 ty2 bw1 size1 bw2 size2)
    pure (.node info kind args)
  | .atom info val =>
    if      val == "%BitWidth1" then pure bw1
    else if val == "%BitWidth2" then pure bw2
    else pure (.atom info val)
  | .ident info rawVal val preresolved =>
    let val ← elabSpecialName2 ty1 ty2 val
    pure (.ident info rawVal val preresolved)

def elabCommand2 (tys1 tys2 : List (String × Syntax × Syntax))
    (cmd : TSyntax `command) : CommandElabM Unit := do
  for (ty1, bw1, size1) in tys1 do
    for (ty2, bw2, size2) in tys2 do
      let cmd' ← elabSpecial2 ty1 ty2 bw1 size1 bw2 size2 cmd
      trace[ScalarElab] "Final declaration for ({ty1}, {ty2}):\n{cmd'}"
      let cmd' ← try liftMacroM (expandNamespacedDeclaration cmd') catch _ => pure cmd'
      Command.elabCommand cmd'

private def uScalarList : CommandElabM (List (String × Syntax × Syntax)) := do
  return [("U8", ←`(8), ←`(1)), ("U16", ←`(16), ←`(2)), ("U32", ←`(32), ←`(4)),
          ("U64", ←`(64), ←`(8)), ("U128", ←`(128), ←`(16)),
          ("Usize", ←`(System.Platform.numBits), ←`(System.Platform.numBits/8))]

private def iScalarList : CommandElabM (List (String × Syntax × Syntax)) := do
  return [("I8", ←`(8), ←`(1)), ("I16", ←`(16), ←`(2)), ("I32", ←`(32), ←`(4)),
          ("I64", ←`(64), ←`(8)), ("I128", ←`(128), ←`(16)),
          ("Isize", ←`(System.Platform.numBits), ←`(System.Platform.numBits/8))]

scoped syntax (name := uuscalarCommand) "uuscalar" command : command

@[command_elab uuscalarCommand]
def uuscalarCommandImpl : CommandElab := fun stx => do
  match stx with
  | `(uuscalarCommand| uuscalar $cmd) => elabCommand2 (←uScalarList) (←uScalarList) cmd
  | _ => throwUnsupportedSyntax

scoped syntax (name := uiscalarCommand) "uiscalar" command : command

@[command_elab uiscalarCommand]
def uiscalarCommandImpl : CommandElab := fun stx => do
  match stx with
  | `(uiscalarCommand| uiscalar $cmd) => elabCommand2 (←uScalarList) (←iScalarList) cmd
  | _ => throwUnsupportedSyntax

scoped syntax (name := iuscalarCommand) "iuscalar" command : command

@[command_elab iuscalarCommand]
def iuscalarCommandImpl : CommandElab := fun stx => do
  match stx with
  | `(iuscalarCommand| iuscalar $cmd) => elabCommand2 (←iScalarList) (←uScalarList) cmd
  | _ => throwUnsupportedSyntax

scoped syntax (name := iiscalarCommand) "iiscalar" command : command

@[command_elab iiscalarCommand]
def iiscalarCommandImpl : CommandElab := fun stx => do
  match stx with
  | `(iiscalarCommand| iiscalar $cmd) => elabCommand2 (←iScalarList) (←iScalarList) cmd
  | _ => throwUnsupportedSyntax

end Aeneas.Std.ScalarElab
