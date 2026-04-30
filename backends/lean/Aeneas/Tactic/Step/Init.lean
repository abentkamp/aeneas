import Lean
import AeneasMeta.Utils
import Aeneas.Std.Primitives
import AeneasMeta.Extensions
import Aeneas.Tactic.Step.Trace
import Aeneas.Std.WP
import AeneasMeta.OptionConfig

namespace Aeneas

namespace Step

open Lean Elab Term Meta
open Utils Extensions

/-!
# Attribute: `step_simps`
-/

/-- The `step_simps` simp attribute. -/
initialize stepSimpExt : SimpExtension ←
  registerSimpAttr `step_simps "\
    The `step_simps` attribute registers simp lemmas to be used by `step`
    to simplify the goal before looking up lemmas. If often happens that some
    monadic function calls, if given some specific parameters (in particuler,
    specific trait instances), can be simplified to far simpler functions: this
    is the main purpose of this attribute."

/-!
# Attribute: `step_pre_simps`
-/

/-- The `step_pre_simps` simp attribute. -/
initialize stepPreSimpExt : SimpExtension ←
  registerSimpAttr `step_pre_simps "\
    The `step_pre_simps` attribute registers simp lemmas to be used by `step`
    when solving preconditions by means of the simplifier."

/-!
# Attribute: `step_post_simps`
-/

/-- The `step_post_simps` simp attribute. -/
initialize stepPostSimpExt : SimpExtension ←
  registerSimpAttr `step_post_simps "\
    The `step_post_simps` attribute registers simp lemmas to be used by `step`
    to post-process post-conditions after introducing them in the context."

/-- The `step_post_simps_proc` simp attribute for the simp rocs. -/
initialize stepPostSimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `step_post_simps_proc "\
    The `step_post_simps_proc` attribute registers simp procedures to be used by `step`
    during its preprocessing phase." none

/-!
# Config
-/

structure Config where
  /- **DO NOT** use this: this is experimental and triggers bugs. -/
  async : Bool := false
  /-- Attempt to discharge preconditions by matching them against local assumptions. -/
  assumTac : Bool := true
  /-- Attempt to infer the ghost variables (variables of step theorems
      that are not bound in the function call). This requires `assumTac` to
      be `true`. -/
  inferGhostVars : Bool := true
  /-- Infer a postcondition for unresolved `?post args...` subgoals left by `progress` -/
  inferPost : Bool := false
  /-- Use `scalar_tac` to discharge preconditions -/
  scalarTac : Bool := false
  /- Use `simp [*]` to discharge preconditions -/
  simpStar : Bool := false
  /-- Use `grind` to discharge preconditions -/
  grind : Bool := true
  /-- Use the ground simp procedures when calling `grind` -/
  withGroundSimprocs : Bool := true
  /--`grind` parameter: see `Lean.Grind.Config` -/
  splits : Nat := 4
  /--`grind` parameter: see `Lean.Grind.Config` -/
  ematch : Nat := 5
  /--`grind` parameter: see `Lean.Grind.Config` -/
  splitMatch : Bool := false
  /--`grind` parameter: see `Lean.Grind.Config` -/
  splitIte : Bool := false
  /--`grind` parameter: see `Lean.Grind.Config` -/
  splitIndPred : Bool := false
  /--`grind` parameter: see `Lean.Grind.Config` -/
  funext : Bool := false
  /--`grind` parameter: see `Lean.Grind.Config` -/
  gen : Nat  := 2
  /--`grind` parameter: see `Lean.Grind.Config` -/
  instances : Nat  := 1000
  /--`grind` parameter: see `Lean.Grind.Config` -/
  canonHeartbeats : Nat := 1000
  /-- Should we use non-linear arithmetic lemmas when calling `grind`? See `Aeneas.Grind.AGrindConfig`. -/
  nla : Bool := true
  /-- Thread a grind state through `step*` calls, reusing simp caches, the e-graph, and
      derived facts across iterations. When `false`, each `step` creates a fresh grind
      call (current behavior). -/
  threadGrindState : Bool := true
  /-- Number of grind preprocessing iterations after internalizing each proposition hypothesis.
      This is the N in `(solvers <|> instantiate [<|> splitNext <|> mbtc]).loop N`. -/
  grindPreprocessIters : Nat := 3
  /-- Allow case splitting (and mbtc) during grind preprocessing. -/
  grindPreprocessSplit : Bool := false
  /-- Run the preprocessing loop (assertAll + solvers) after internalizing each proposition
      hypothesis. When `false`, hypotheses are added to the e-graph but satellite solvers
      and e-matching (`instantiate`) are not run until discharge time. -/
  preprocessGrind : Bool := false
deriving Repr

def Config.toGrindConfig (cfg : Config) : Grind.Config :=
  let { async := _, assumTac := _, inferGhostVars := _, inferPost := _, scalarTac := _, simpStar := _,
        grind := _, withGroundSimprocs := _, nla := _,
        threadGrindState := _, grindPreprocessIters := _, grindPreprocessSplit := _,
        preprocessGrind := _,
        splits, ematch, splitMatch, splitIte, splitIndPred, funext, gen, instances, canonHeartbeats } := cfg
  { splits, ematch, splitMatch, splitIte, splitIndPred, funext, gen, instances, canonHeartbeats }

declare_option_config_elab Config elabPartialConfig aeneas.step

/-! # Step State (threaded through `step*`) -/

/-- State threaded through `step*` iterations when `threadGrindState = true`.
    Contains the grind state layers needed to resume `GrindM` operations. -/
structure StepGrindState where
  /-- GrindM-level state (caches: simp state, congruence theorems, hash-consing) -/
  grindState : Grind.State
  /-- Sym-level state (hash-consing, inferType cache, congrInfo cache).
      Must be preserved alongside `grindState` — `GrindM.run` creates a fresh
      `Sym.State` each time, so without explicit save/restore the e-graph's
      pointer-equality-based proof reconstruction breaks. -/
  symState : Lean.Meta.Sym.State
  /-- Sym-level context (hash-consed SharedExprs: True, False, 0, etc.).
      Must be preserved across runs — the e-graph uses pointer equality on
      these expressions, so recreating them (via a new `SymM.run`) breaks lookups. -/
  symCtx : Lean.Meta.Sym.Context
  /-- Grind-level context (config, simpMethods, extensions, etc.).
      Must be preserved across runs — rebuilt `Grind.Context` may produce
      structurally equal but pointer-different internal values. -/
  grindCtx : Grind.Context
  /-- Grind methods reference (propagators, etc.).
      Must be preserved across runs — contains IO.Refs that the e-graph depends on. -/
  methodsRef : Grind.MethodsRef
  /-- The knowledge base: e-graph, accumulated facts, e-matching state.
      Decoupled from any MVarId — can be shared across goals. -/
  goalState : Grind.GoalState
  /-- Whether preprocessing derived a contradiction during internalization.
      If `true`, the e-graph already contains `False` — discharge can succeed
      trivially on any precondition. -/
  contradiction : Bool := false
  /-- Proof of `False` derived from contradicting hypotheses in the local context.
      Set when grind finds a contradiction during context internalization and
      preprocessing of the grind state (in both `initStepGrindState` and
      `updateStepGrindState`). The proof comes from a fresh mvar with target `False`
      that grind closed. Callers use `closeGoalWithFalse` to derive a proof of the
      real goal's type via `False.elim`. -/
  contradictionProof? : Option Expr := none
  /-- Parameters (config, simp context, extensions, etc.) -/
  params : Grind.Params
  /-- Cached Aeneas simp context (expensive to build — cached at init). -/
  simpCtx : Simp.Context
  /-- Cached Aeneas simprocs array (expensive to build — cached at init). -/
  simprocs : Simp.SimprocsArray

/-- Top-level state threaded through `step*` iterations.
    When `threadGrindState = false`, `grindState?` stays `none` and
    every `step` call creates a fresh grind context. -/
structure StepState where
  /-- Optional grind state. `none` when threading is disabled or not yet initialized. -/
  grindState? : Option StepGrindState := none

/-- Get the contradiction proof from the grind state, if any.
    Returns `some falseProof` when grind found contradicting hypotheses during
    the last `init` or `update` call. Use `closeGoalWithFalse` to close the goal. -/
def StepState.contradictionProof? (state : StepState) : Option Expr :=
  state.grindState?.bind (·.contradictionProof?)

/-! # Attribute: `step` -/

structure StepSpecDesc where
  -- The universally quantified variables and preconditions, as mvars
  preconds : Array MVarId
  -- The existentially quantified variables
  evars : Array FVarId
  -- The function applied to its arguments
  fArgsExpr : Expr
  -- ⊤ if the function is a constant (must be if we are registering a theorem,
  -- but is not necessarily the case if we are looking at a goal)
  fIsConst : Bool
  -- The function arguments
  fLevels : List Level
  args : Array Expr
  -- The returned value
  ret : Expr
  -- The postcondition (if there is)
  postcond? : Option Expr

section Methods
  variable {m} [MonadControlT MetaM m] [Monad m]
  variable {a : Type}

  /- Auxiliary helper.

     Given type `α₀ × ... × αₙ`, introduce fresh variables
     `x₀ : α₀, ..., xₙ : αₙ` and call the continuation with those.
  -/
  def withFreshTupleFieldFVars [Inhabited a] (basename : Name) (ty : Expr) (k : Array Expr → m a) : m a := do
    let tys := destProdsType ty
    let tys := List.map (fun (ty, i) => (Name.num basename i, fun _ => pure ty)) (List.zipIdx tys)
    withLocalDeclsD ⟨ tys ⟩ k
end Methods

/-- Returns true if `f` is the spec-head constant `Std.WP.spec`. The
    unified `spec` combinator handles both total-correctness specs and
    branch-by-branch (`ok`/`fail`/`div`) specs through the same head; the
    distinction lives in the postcondition. -/
def isSpecHead (f : Expr) : Bool :=
  f.isConstOf ``Std.WP.spec

/- Analyze a goal or a step theorem to decompose its arguments.

  StepSpec theorems should be of the following shape:
  ```
  ∀ x1 ... xn, H1 → ... Hn → spec (f x1 ... xn) P
  ```
-/
def getStepSpecFunArgsExpr (ty : Expr) :
  MetaM Expr := do
  let ty := ty.consumeMData
  unless ← isProp ty do
    throwError "Expected a proposition, got {←inferType ty}"
  -- ty == ∀ xs, spec (f x1 ... xn) P
  let (xs, xs_bi, ty₂) ← forallMetaTelescope ty
  trace[Step] "Universally quantified arguments and assumptions: {xs}"
  -- ty₂ == spec (f x1 ... xn) P
  let (spec?, args) := ty₂.consumeMData.withApp (fun f args => (f, args))
  if isSpecHead spec? ∧ args.size = 3
  then pure args[1]! -- this is `f x1 ... xn`
  else throwError "Expected to be a `spec (f x1 ... xn) P`, got {ty₂}"

structure Rules where
  rules : DiscrTree Name
  /- We can't remove keys from a discrimination tree, so to support
     local rules we keep a set of deactivated rules (rules which have
     come out of scope) on the side -/
  deactivated : Std.HashSet Name
deriving Inhabited

def Rules.empty : Rules := ⟨ DiscrTree.empty, Std.HashSet.emptyWithCapacity ⟩

def Extension := SimpleScopedEnvExtension (DiscrTreeKey × Name) Rules
deriving Inhabited

def Rules.insert (r : Rules) (kv : Array DiscrTree.Key × Name) : Rules :=
  { rules := r.rules.insertKeyValue kv.fst kv.snd,
    deactivated := r.deactivated.erase kv.snd }

def Rules.erase (r : Rules) (k : Name) : Rules :=
  { r with deactivated := r.deactivated.insert k }

def mkExtension (name : Name := by exact decl_name%) :
  IO Extension :=
  registerSimpleScopedEnvExtension {
    name        := name,
    initial     := Rules.empty,
    addEntry    := Rules.insert,
  }

/-- The step attribute -/
structure StepSpecAttr where
  attr : AttributeImpl
  ext  : Extension
  deriving Inhabited

/-- (Currently a pass-through.) Placeholder for normalizing negation
    preconditions like `¬ (a ≥ b) ↦ a < b`. The raw `¬ P_fail` form is
    passed straight through; step's `grind` discharge handles the
    semantic conversion at use-time. A future improvement would
    construct the equivalent positive form *and* the corresponding proof
    transformation, so the user-facing precondition matches the
    historical hand-written shape verbatim. -/
private def normalizeNeg (e : Expr) : MetaM Expr := pure e

/-- Build the partial-spec `_step` companion: walks each Error constructor,
    emitting one precondition per non-trivial fail arm; ditto for div.
    See `generateStepAlias` for the user-visible behavior. -/
private def buildPartialStepAlias (stx : Syntax) (thName : Name) (sig : ConstantVal)
    (fvars : Array Expr) (specArgs : Array Expr) (postExpr thApp : Expr)
    (stepName : Name) : MetaM TheoremVal := do
  let xExpr := specArgs[1]!
  let xType ← inferType xExpr
  let some α := xType.consumeMData.getAppArgs[0]?
    | throwError "Expected `xExpr : Result α`, got {xType}"
  -- Enumerate Error constructors and build per-ctor preconditions.
  let errorIndInfo ← getConstInfoInduct ``Aeneas.Std.Error
  -- Track each non-trivial fail constructor: full ctor name, hypothesis
  -- binder name, hypothesis type. Used to drive both the precondition
  -- list and the term-mode `Error.casesOn` proof construction.
  let mut failPreconds : Array (Name × Name × Expr) := #[]
  for ctorName in errorIndInfo.ctors do
    let failOfCtor := Lean.mkConst ctorName
    let failExpr ← mkAppOptM ``Aeneas.Std.Result.fail #[some α, some failOfCtor]
    let pFail ← Meta.whnfD (Lean.Expr.beta postExpr #[failExpr])
    if pFail.isConstOf ``False then
      continue
    let neg ← normalizeNeg (← mkAppM ``Not #[pFail])
    let hypName := Name.mkSimple s!"h_{ctorName.getString!}"
    failPreconds := failPreconds.push (ctorName, hypName, neg)
  -- Div arm.
  let divExpr ← mkAppOptM ``Aeneas.Std.Result.div #[some α]
  let pDiv ← Meta.whnfD (Lean.Expr.beta postExpr #[divExpr])
  let divPrecond? : Option Expr ← if pDiv.isConstOf ``False then pure none else
    some <$> normalizeNeg (← mkAppM ``Not #[pDiv])
  -- Build the success post body by reducing P (.ok z).
  let pOkLam ← withLocalDeclD `z α fun z => do
    let okExpr ← mkAppOptM ``Aeneas.Std.Result.ok #[some α, some z]
    let pOkApp ← Meta.whnfD (Lean.Expr.beta postExpr #[okExpr])
    mkLambdaFVars #[z] pOkApp
  -- Introduce the per-arm precondition fvars in order.
  let rec buildWithPreconds (i : Nat) (acc : Array Expr)
      (k : Array Expr → MetaM TheoremVal) : MetaM TheoremVal := do
    if h : i < failPreconds.size then
      let (_, n, ty) := failPreconds[i]
      withLocalDeclD n ty fun fv => buildWithPreconds (i + 1) (acc.push fv) k
    else
      match divPrecond? with
      | some divTy => withLocalDeclD `h_div divTy fun fv => k (acc.push fv)
      | none => k acc
  buildWithPreconds 0 #[] fun precondFvars => do
    -- Construct the proof of `partial_to_success_with_hyps`.
    -- - h_ok: fun z h => h (since reduced ok arm = success post body).
    let hOk ← withLocalDeclD `z α fun z => do
      let okExpr ← mkAppOptM ``Aeneas.Std.Result.ok #[some α, some z]
      let pOkRaw := Lean.Expr.beta postExpr #[okExpr]
      withLocalDeclD `h pOkRaw fun h => do
        mkLambdaFVars #[z, h] h
    -- - h_no_fail: ∀ e, ¬ P (.fail e). Built term-mode via `Error.casesOn`
    --   with one branch per `Error` constructor:
    --     * supplied ctors (h_arrayOutOfBounds, h_maximumSizeExceeded, …)
    --       ↦ apply the user's hypothesis to `h`,
    --     * un-supplied ctors fall through to the macro's `_ => False`
    --       arm so `h : False` ↦ `h.elim`.
    --   Predictable; no tactic discharge needed.
    let hNoFail ← withLocalDeclD `e (Lean.mkConst ``Aeneas.Std.Error) fun e => do
      withLocalDeclD `h
          (Lean.Expr.beta postExpr
              #[← mkAppOptM ``Aeneas.Std.Result.fail #[some α, some e]])
          fun h => do
        let motive ← withLocalDeclD `e' (Lean.mkConst ``Aeneas.Std.Error) fun e' => do
          let failOfE' ← mkAppOptM ``Aeneas.Std.Result.fail #[some α, some e']
          let pFail' := Lean.Expr.beta postExpr #[failOfE']
          mkLambdaFVars #[e'] (← mkAppM ``Not #[pFail'])
        -- Map ctor name → user fvar (if any).
        let lookupHyp (ctorName : Name) : Option Expr := Id.run do
          let mut idx : Option Nat := none
          for h : i in [0:failPreconds.size] do
            if failPreconds[i].1 == ctorName then idx := some i
          idx.bind fun i =>
            if h : i < precondFvars.size then some precondFvars[i] else none
        let mut branches : Array Expr := #[]
        for ctorName in errorIndInfo.ctors do
          let failOfCtor := Lean.mkConst ctorName
          let failExpr ← mkAppOptM ``Aeneas.Std.Result.fail #[some α, some failOfCtor]
          let pFail := Lean.Expr.beta postExpr #[failExpr]
          let pFailReduced ← Meta.whnfD pFail
          let branch ← withLocalDeclD `h pFailReduced fun hLocal => do
            match lookupHyp ctorName with
            | some userHyp => mkLambdaFVars #[hLocal] (mkApp userHyp hLocal)
            | none =>
                -- catch-all branch: `pFailReduced` is `False` (or
                -- definitionally so). Conclusion type is also `False`.
                -- `fun (h : False) => h` (i.e. `id`) suffices.
                mkLambdaFVars #[hLocal] hLocal
          branches := branches.push branch
        let casesProof ← mkAppOptM ``Aeneas.Std.Error.casesOn
          (#[some motive, some e] ++ branches.map some)
        let inner := mkApp casesProof h
        mkLambdaFVars #[e, h] inner
    -- - h_no_div: ¬ P .div. If catch-all, P .div ↝ False, so `fun h => h.elim`.
    --   Otherwise apply user-supplied div hypothesis directly.
    let hNoDiv ← withLocalDeclD `h
        (Lean.Expr.beta postExpr
            #[← mkAppOptM ``Aeneas.Std.Result.div #[some α]])
        fun h => do
      match divPrecond? with
      | some _ =>
          -- The user-supplied h_div fvar is the LAST element of precondFvars.
          if hi : 0 < precondFvars.size then
            let userDiv := precondFvars[precondFvars.size - 1]'
              (Nat.sub_lt hi (by decide))
            mkLambdaFVars #[h] (mkApp userDiv h)
          else
            throwError "Inconsistent state: divPrecond? set but no fvar"
      | none =>
          -- `h : False` (catch-all). Conclusion is `False`. `h` itself
          -- has the right type — no `False.elim` needed.
          mkLambdaFVars #[h] h
    let proof ← mkAppM ``Aeneas.Std.WP.partial_to_success_with_hyps
      #[thApp, hOk, hNoFail, hNoDiv]
    let allFvars := fvars ++ precondFvars
    let value ← mkLambdaFVars allFvars proof
    let concl ← do
      let successPost ← mkAppM ``Aeneas.Std.WP.successPost #[pOkLam]
      mkAppM ``Aeneas.Std.WP.spec #[xExpr, successPost]
    let ty ← mkForallFVars allFvars concl
    pure ({ name := stepName, levelParams := sig.levelParams, type := ty,
            value := value : TheoremVal })

/-- Synthesize a `<thName>_step` companion of the original theorem in the
    success-only `successPost _` form, suitable for the existing `step`
    tactic pipeline. For success-only sources, this is just an alias. For
    partial-spec sources `spec x P`, the synthesized companion enumerates
    each `Error` constructor:
    - For each constructor whose `P (.fail .ctor)` is non-trivial (does not
      reduce to `False`), emit a precondition named after the constructor
      (`h_arrayOutOfBounds`, `h_maximumSizeExceeded`, ...).
    - The `div` arm gets a `h_div` precondition if non-trivial.
    Each precondition is normalized via `[not_le, not_lt, not_not]` so
    `¬ (i.val ≥ v.length)` becomes `i.val < v.length`, matching the
    historical hand-written success-only spec shape.
    The conclusion is `spec x (successPost (fun z => P (.ok z)))`, with
    `P (.ok z)` iota-reduced to the ok-arm body. -/
private def generateStepAlias (stx : Syntax) (thName : Name) : MetaM Name := do
  let env ← getEnv
  let some decl := env.findAsync? thName
    | throwError "Could not find theorem {thName}"
  let sig := decl.sig.get
  let stepName := thName.appendAfter "_step"
  let levelArgs := sig.levelParams.map Level.param
  let thConst := Lean.mkConst thName levelArgs
  let normalizedType ← normalizeLetBindings sig.type
  let auxDecl ← forallTelescope normalizedType fun fvars body => do
    let bodyApp := body.consumeMData
    let (specHead, specArgs) := bodyApp.withApp (fun f args => (f, args))
    unless specHead.isConstOf ``Aeneas.Std.WP.spec ∧ specArgs.size = 3 do
      throwError "Expected source body `spec _ _`, got {body}"
    let postExpr := specArgs[2]!.consumeMData
    let thApp := mkAppN thConst fvars
    if postExpr.isAppOfArity ``Aeneas.Std.WP.successPost 2 then
      -- Success-only source: emit a plain alias.
      let ty ← mkForallFVars fvars body
      let value ← mkLambdaFVars fvars thApp
      pure ({ name := stepName, levelParams := sig.levelParams, type := ty, value : TheoremVal })
    else
      buildPartialStepAlias stx thName sig fvars specArgs postExpr thApp stepName
  addDecl (.thmDecl auxDecl)
  addDeclarationRangesFromSyntax stepName stx
  pure stepName

/-- Synthesize an mvcgen-friendly companion `<thName>_mvcgen` of the form
    `⦃ ⌜True⌝ ⦄ f x ⦃ ... ⦄`. Detects whether the source post is in
    `successPost _` (success-only) form or general (partial-spec) form and
    chooses the appropriate lifting lemma. The companion is tagged `@[spec]`
    so mvcgen finds it. -/
private def generateMvcgenSpec (stx : Syntax) (attrKind : AttributeKind)
    (thName : Name) : MetaM Unit := do
  let env ← getEnv
  let some decl := env.findAsync? thName
    | throwError "Could not find theorem {thName}"
  let sig := decl.sig.get
  -- Specialise all universe level parameters to 0 so that the lifting lemmas
  -- (whose `α : Type`) apply.
  let zeroLevels := List.replicate sig.levelParams.length Level.zero
  let ty ← normalizeLetBindings (sig.type.instantiateLevelParams sig.levelParams zeroLevels)
  forallTelescope ty fun fvars body => do
    -- body should be `spec (f args) post`.
    let bodyApp := body.consumeMData
    let (specHead, specArgs) := bodyApp.withApp (fun f args => (f, args))
    unless specHead.isConstOf ``Aeneas.Std.WP.spec ∧ specArgs.size = 3 do
      throwError "Expected a `spec _ _` body, got {body}"
    let postExpr := specArgs[2]!
    let liftLemma :=
      if postExpr.consumeMData.isAppOfArity ``Aeneas.Std.WP.successPost 2
      then ``Aeneas.Std.WP.spec_to_mvcgen
      else ``Aeneas.Std.WP.spec_to_mvcgen_partial
    let thConst := Lean.mkConst thName zeroLevels
    let thApp := mkAppN thConst fvars
    let proof ← mkAppM liftLemma #[thApp]
    let innerTy ← inferType proof
    let proofTerm ← mkLambdaFVars fvars proof
    let thmTy ← mkForallFVars fvars innerTy
    let mvcgenName := thName.appendAfter "_mvcgen"
    let auxDecl : TheoremVal := {
      name        := mvcgenName
      levelParams := []
      type        := thmTy
      value       := proofTerm
    }
    addDecl (.thmDecl auxDecl)
    addDeclarationRangesFromSyntax mvcgenName stx
    Lean.Attribute.add mvcgenName `spec .missing attrKind

private def saveStepSpecFromThm (ext : Extension) (attrKind : AttributeKind)
    (stx : Syntax) (thName : Name) : AttrM Unit := do
  -- Lookup the theorem
  let env ← getEnv
  -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
  attrIgnoreAuxDef thName (pure ()) do
    trace[Step] "Registering `step` theorem for {thName}"
    let some thDecl := env.findAsync? thName
      | throwError "Could not find theorem {thName}"
    let type := thDecl.sig.get.type
    let fKey ← MetaM.run' (do
      trace[Step] "Theorem: {type}"
      -- Normalize to eliminate the let-bindings
      let ty ← normalizeLetBindings type
      trace[Step] "Theorem after normalization (to eliminate the let bindings): {ty}"
      let fExpr ← getStepSpecFunArgsExpr ty
      trace[Step] "Registering spec theorem for expr: {fExpr}"
      -- Convert the function expression to a discrimination tree key
      DiscrTree.mkPath fExpr)
    -- Synthesize the `_step` alias and register it (instead of the original)
    -- with the step DiscrTree.
    let stepName ← MetaM.run' (generateStepAlias stx thName)
    ScopedEnvExtension.add ext (fKey, stepName) attrKind
    trace[Step] "Saved the entry under {stepName}"
    -- Synthesize the `_mvcgen` companion and tag it `@[spec]`.
    try
      MetaM.run' (generateMvcgenSpec stx attrKind thName)
    catch e =>
      logWarning m!"Could not generate mvcgen companion for {thName}: {e.toMessageData}"
    pure ()

/- Initiliaze the `step` attribute. -/
initialize stepAttr : StepSpecAttr ← do
  let ext ← mkExtension `stepMap
  let attrImpl : AttributeImpl := {
    name := `step
    descr := "Adds theorems to the `step` database"
    add := fun thName stx attrKind => do
      Attribute.Builtin.ensureNoArgs stx
      saveStepSpecFromThm ext attrKind stx thName
    erase := fun thName => do
      let s := ext.getState (← getEnv)
      let s := s.erase thName
      modifyEnv fun env => ext.modifyState env fun _ => s
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

def StepSpecAttr.find? (s : StepSpecAttr) (e : Expr) : MetaM (Array Name) := do
  let state := s.ext.getState (← getEnv)
  let rules ← state.rules.getMatch e
  pure (rules.filter (fun th => th ∉ state.deactivated))

def StepSpecAttr.getState (s : StepSpecAttr) : MetaM Rules := do
  pure (s.ext.getState (← getEnv))

def showStoredStepThms : MetaM Unit := do
  let st ← stepAttr.getState
  -- TODO: how can we iterate over (at least) the values stored in the tree?
  --let s := st.toList.foldl (fun s (f, th) => f!"{s}\n{f} → {th}") f!""
  let s := f!"{st.rules}, {st.deactivated.toArray}"
  IO.println s

/-! # Attribute: `step_pure` -/

namespace Test
  /-!
  Making some tests here as models to guide the automation generation of proof terms when lifting theorems in `step_pure`
  -/
  open Std Result
  def pos_pair : Int × Int := (0, 1)

  theorem pos_pair_is_pos :
    let (x, y) := pos_pair
    x ≥ 0 ∧ y ≥ 0 := by simp [pos_pair]

  theorem lifted_is_pos :
    ∃ x y, lift pos_pair = ok (x, y) ∧
    x ≥ 0 ∧ y ≥ 0 :=
  (match pos_pair with
  | (x, y) =>
    fun (h : match (x, y) with | (x, y) => x ≥ 0 ∧ y ≥ 0) =>
    Exists.intro x (Exists.intro y (And.intro (Eq.refl (ok (x, y))) h))
  : ∀ (_ : match pos_pair with | (x, y) => x ≥ 0 ∧ y ≥ 0),
    ∃ x y, lift pos_pair = ok (x, y) ∧
    x ≥ 0 ∧ y ≥ 0) pos_pair_is_pos

  /- Same as `lifted_is_pos` but making the implicit parameters of the `Exists.intro` explicit:
     this is the important part. -/
  theorem lifted_is_pos' :
    ∃ x y, lift pos_pair = ok (x, y) ∧
    x ≥ 0 ∧ y ≥ 0 :=
  (match pos_pair with
  | (x, y) =>
    fun (h : match (x, y) with | (x, y) => x ≥ 0 ∧ y ≥ 0) =>
    @Exists.intro Int (fun x_1 => ∃ y_1, ok (x, y) = ok (x_1, y_1) ∧ x_1 ≥ 0 ∧ y_1 ≥ 0)
      x (@Exists.intro Int (fun y_1 => ok (x, y) = ok (x, y_1) ∧ x ≥ 0 ∧ y_1 ≥ 0)
        y (@And.intro (ok (x, y) = ok (x, y)) _ (Eq.refl (ok (x, y))) h))
  : ∀ (_ : match pos_pair with | (x, y) => x ≥ 0 ∧ y ≥ 0),
    ∃ x y, lift pos_pair = ok (x, y) ∧
    x ≥ 0 ∧ y ≥ 0) pos_pair_is_pos

  def pos_triple : Int × Int × Int := (0, 1, 2)

  theorem pos_triple_is_pos :
    let (x, y, z) := pos_triple
    x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 := by simp [pos_triple]

  structure U8 where
    val : Nat

  def overflowing_add (x y : U8) : U8 × Bool := (⟨ x.val + y.val ⟩, x.val + y.val > 255)

  theorem overflowing_add_eq (x y : U8) :
    let z := overflowing_add x y
    if x.val + y.val > 255 then z.snd = true
    else z.snd = false
    :=
    by simp [overflowing_add]

end Test

theorem spec_lift {α : Type} (x : α) (P : α → Prop) (h : P x) :
  Std.WP.spec (Std.lift x) (Std.WP.successPost P) := by
  simp [Std.lift, Std.WP.successPost]
  apply h

def reduceProdProjs (e : Expr) : MetaM Expr := do
  let pre (e : Expr) : MetaM TransformStep := do
    trace[Utils] "Attempting to reduce: {e}"
    match ← reduceProj? e with
    | none =>
      e.withApp fun fn args =>
      if fn.isConst ∧ (fn.constName! = ``Prod.fst ∨ fn.constName! = ``Prod.snd) ∧ args.size = 3 then
        let pair := args[2]!
        pair.withApp fun fn' args =>
          if fn'.isConst ∧ fn'.constName! = ``Prod.mk ∧ args.size = 4 then
            if fn.constName! = ``Prod.fst then pure (.continue args[2]!)
            else pure (.continue args[3]!)
          else pure (.continue e)
      else pure (.continue e)
    | some e =>
      trace[Utils] "reduced: {e}"
      pure (.continue e)
  transform e (pre := pre)

open Std.WP

theorem intro_predn (p : α × β → Prop) : p = predn (fun x y => p (x, y)) := by
  unfold predn
  simp only

theorem lift_to_spec x (p0 p1 : α → Prop) (h0 : p0 x) (h1 : p0 = p1) :
    spec (Std.lift x) (successPost p1) := by
  grind [spec, Std.lift, successPost]

namespace Test

  /-- Example which shows how to write the proof term explicitly -/
  theorem test_pos_triple (pos_triple : Nat × Nat × Nat) (thm : (fun (x, y, z) => x > 0 ∧ y > 0 ∧ z > 0) pos_triple) :
    Std.lift pos_triple ⦃ x y z => x > 0 ∧ y > 0 ∧ z > 0 ⦄ := by
    --
    have h := fun x => intro_predn (fun y => match (x, y) with | (x, y, z) => x > 0 ∧ y > 0 ∧ z > 0)
    --
    have h' := intro_predn (fun (x, y, z) => x > 0 ∧ y > 0 ∧ z > 0)
    replace h := congrArg predn (funext h)
    replace h := Eq.trans h' h
    clear h'
    --
    replace h := lift_to_spec pos_triple (fun (x, y, z) => x > 0 ∧ y > 0 ∧ z > 0)
      (predn fun x => predn fun x_1 y => match (x, x_1, y) with | (x, y, z) => x > 0 ∧ y > 0 ∧ z > 0)
      thm h
    exact h

  /-- Example which uses tactics -/
  theorem test_pos_triple' (pos_triple : Nat × Nat × Nat) (thm : (fun (x, y, z) => x > 0 ∧ y > 0 ∧ z > 0) pos_triple) :
    Std.lift pos_triple ⦃ x y z => x > 0 ∧ y > 0 ∧ z > 0 ⦄ := by
    simp -failIfUnchanged -iota only [_root_.Aeneas.Std.lift, _root_.Aeneas.Std.WP.spec_ok, _root_.Aeneas.Std.WP.predn] at thm ⊢
    exact thm

end Test

/-- Given a theorem type `P x` and a pattern of the shape `∃ y₀ ... yₙ, x = (y₀, ..., yₙ)`,
    generate a theorem type of the shape:
    ```lean
    spec (lift x) (fun y₀ ... yₙ => P (y₀, ..., yₙ))
    ```
    that is, using syntactic sugar:
    ```lean
    (lift x) ⦃ fun y₀ ... yₙ => P (y₀, ..., yₙ) ⦄
    ```

    Note that the pattern is optional: if the user doesn't provide it, we completely decompose
-/
def liftThmType (thmTy : Expr) (pat : Option Syntax)
  /- `mkPat` generates the pattern to use to guide the replacement.

  For instance: `∃ x y, foo a = (x, y)`
   -/
  (mkPat : Array Expr → Expr → MetaM Expr)
  /- `mkPred` receives:
    - the type of the definition/theorem after stripping the quantifiers
    - the pattern
    - the new pattern (can be `(y₀, ..., yₙ)` for instance)
    - the parameters of the definition

    and should generate the: `P (y₀, ..., yₙ)`)
   -/
  (mkPred : Expr → Expr → Expr → Array Expr → MetaM Expr) :
  MetaM Expr := do
  withTraceNode `Step (fun _ => pure m!"liftThmType") do
  /- Strip the quantifiers *before* elaborating the pattern -/
  forallTelescope thmTy.consumeMData fun fvars thmTy => do
  let pat ← do
    match pat with
    | none => mkPat fvars thmTy
    | some pat => do
      pure ((← Elab.Term.elabTerm pat none |>.run).fst)
  trace[Step] "Elaborated pattern: {pat}"
  existsTelescope pat.consumeMData fun _ patEq => do
  trace[Step] "patEq: {patEq}"
  /- Destruct the equality. Note that there may not be an equality, in which case
     we see the type as a tuple and introduce one variable per field of the tuple
     (and a single variable if it is actually not a tuple). -/
  let tryDestEq basename (eq : Expr) (k : Expr → Expr → MetaM Expr) : MetaM Expr := do
    match ← destEqOpt eq with
    | some (x, y) => k x y
    | none =>
      withFreshTupleFieldFVars (.str .anonymous basename) (← inferType pat) fun fvars => do
      k pat (← mkProdsVal fvars.toList)
  tryDestEq "x" patEq fun pat fvarsPat => do
  trace[Step] "Decomposed patterns: pat: {pat}, fvarsPat: {fvarsPat}"
  /- The decomposed pattern should be tuple a expression: decompose it further into a list of variables -/
  let patFVars : Array Expr := ⟨ destProdsVal fvarsPat ⟩
  /- Substitute the pattern -/
  let thmTy ← mkPred thmTy pat fvarsPat fvars
  trace[Step] "Theorem after substituting the pattern: {thmTy}"
  /- Create the nested `predn` -/
  let rec mkPredn (fvars : List Expr) : MetaM Expr := do
    withTraceNode `Step (fun _ => pure m!"mkPredn: fvars: {fvars}") do
    match fvars with
    | [] => throwError "Unexpected"
    | [x] =>
      trace[Progres] "Introducing a single lambda: x: {x}, thmTy: {thmTy}"
      mkLambdaFVars #[x] thmTy
    | x :: fvars => do
      trace[Progres] "Introducing `predn`: x: {x}"
      let thm ← mkPredn fvars
      trace[Progres] "thm: {thm}"
      mkAppM ``predn #[← mkLambdaFVars #[x] thm]
  let thmTy ← mkPredn patFVars.toList
  trace[Step] "result of mkPredn: {thmTy}"
  /- Add the `spec` (wrapped in `successPost` to match the success-only
     macro expansion) -/
  let liftExpr ← mkAppM ``Std.lift #[pat]
  trace[Step] "liftExpr: {liftExpr}"
  let thmTy ← mkAppM ``successPost #[thmTy]
  let thmTy ← mkAppM ``spec #[liftExpr, thmTy]
  trace[Step] "thmTy after introducing `spec`: {thmTy}"
  /- Reintroduce the universal quantifiers -/
  let thmTy ← mkForallFVars fvars thmTy
  trace[Step] "thmTy after introducing the quantifiers: {thmTy}"
  pure thmTy


def liftThmReplaceInTy (thm0 pat npat : Expr) (_ : Array Expr) : MetaM Expr := do
  let thm ← mapVisit (fun _ e => do if e == pat then pure npat else pure e) thm0
  /- Reduce a bit the expression, but in a controlled manner, to make it cleaner -/
  let thm ← normalizeLetBindings thm
  reduceProdProjs thm

def liftThm (stx : Syntax) (name : Name) (pat : Option (TSyntax `term))
  (mkPat : Array Expr → Expr → MetaM Expr := fun _ _ => failure)
  (mkPred := liftThmReplaceInTy)
  (suffix : String := "step_spec")
  (tacticStx : Option (TSyntax `tactic) := none)
  : MetaM Name := do
  trace[Step] "Name: {name}"
  let env ← getEnv
  let some decl := env.findAsync? name
    | throwError "Could not find declaration {name}"
  let sig := decl.sig.get
  -- Generate the type of the theorem
  let thmTy ← liftThmType sig.type pat mkPat mkPred
  trace[Step] "thmTy: {thmTy}"
  -- Prove the theorem - we keep things simple by calling a tactic
  let mvar ← mkFreshExprSyntheticOpaqueMVar thmTy
  let tacticStx ← do
    match tacticStx with
    | none =>
      `(tactic|
        simp -failIfUnchanged -iota only
          [_root_.Aeneas.Std.lift, _root_.Aeneas.Std.WP.spec_ok, _root_.Aeneas.Std.WP.predn] <;>
        exact $(mkIdent name))
    | some stx => pure stx
  let (goals, _) ← runTactic mvar.mvarId! tacticStx
  if goals.length > 0 then throwError "Could not prove the theorem"
  --
  let name := Name.str name suffix
  let auxDecl : TheoremVal := {
    name
    levelParams := sig.levelParams
    type := thmTy
    value := ← instantiateMVars mvar
  }
  addDecl (.thmDecl auxDecl)
  /- Save the range -/
  addDeclarationRangesFromSyntax name stx
  --
  pure name

/-!
# Command: `#step_pure_lift_thm`

We do not really use it - it is mostly for testing purposes.
-/

elab stx:"#step_pure_lift_thm" id:ident pat:term : command => do
  Lean.Elab.Command.runTermElabM fun _ => do
  let some cs ← Term.resolveId? id | throwError m!"Unknown id: {id}"
  let name := cs.constName!
  let _ ← liftThm stx name pat

namespace Test
  #step_pure_lift_thm pos_pair_is_pos (∃ x y, pos_pair = (x, y))

  /--
info: Aeneas.Step.Test.pos_pair_is_pos.step_spec :
  Std.lift pos_pair ⦃ x y =>
    match (x, y) with
    | (x, y) => x ≥ 0 ∧ y ≥ 0 ⦄
  -/
  #guard_msgs in
  #check pos_pair_is_pos.step_spec

  #step_pure_lift_thm pos_triple_is_pos pos_triple

  /--
info: Aeneas.Step.Test.pos_triple_is_pos.step_spec :
  Std.lift pos_triple ⦃ x.0 x.1 x.2 =>
    match (x.0, x.1, x.2) with
    | (x, y, z) => x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ⦄
  -/
  #guard_msgs in
  #check pos_triple_is_pos.step_spec

  def pos_triple_is_pos' := pos_triple_is_pos
  #step_pure_lift_thm pos_triple_is_pos' (∃ z, pos_triple = z)

  /--
info: Aeneas.Step.Test.pos_triple_is_pos'.step_spec :
  Std.lift pos_triple ⦃ z =>
    match z with
    | (x, y, z) => x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ⦄
  -/
  #guard_msgs in
  #check pos_triple_is_pos'.step_spec

  #step_pure_lift_thm overflowing_add_eq (overflowing_add x y)

  /--
info: Aeneas.Step.Test.overflowing_add_eq.step_spec (x y : U8) :
  Std.lift (overflowing_add x y) ⦃ x.0 x.1 => if x.val + y.val > 255 then x.1 = true else x.1 = false ⦄
  -/
  #guard_msgs in
  #check overflowing_add_eq.step_spec
end Test

/-!
# Attribute: `#step_pure`
-/

syntax (name := step_pure) "step_pure" term : attr

section
  variable {m : Type → Type} [Monad m] [MonadOptions m] [MonadTrace m] [AddMessageContext m] [MonadError m]

  partial def parseCommaSeparated (isTuple : Bool) (stx : Syntax) (acc : Array Syntax := #[]) :
    m (Array Syntax) := do
    trace[StepElab] "parsing comma separated: {stx} with acc: {acc}"
    -- TODO: check if ident
    match stx with
    | `(ident| $name:ident) =>
      trace[StepElab] "is an ident"
      pure (acc.push stx)
    | _ =>
      trace[StepElab] "not an ident"
      let args := stx.getArgs
      trace[StepElab] "args.size: {args.size}"
      /- Parsing is not the same if we have `(...)` or `⟨ ... ⟩`:
        - in the first case, the syntax looks like this (we have nested lists): `["x", "," ["y", ...]]`
        - in the second case, the syntax looks like this (the list is flattened): `["x", ",", "y", ...]`
        -/
      if args.size = 0 then pure acc
      else if h: args.size = 1 then pure (acc.push args[0])
      else if h: isTuple ∧ args.size = 3 then
        let arg0 := args[0]
        let arg1 := args[1]
        let arg2 := args[2]
        trace[StepElab] "parsing comma separated:\n- arg0: {arg0}\n- arg1: {arg1}\n- arg2: {arg2}"
        let isComma ← do
          match arg1 with
          | .atom _ "," => pure true
          | _ => pure false
        if isComma then
          trace[StepElab] "arg1 is a comma"
          parseCommaSeparated isTuple arg2 (acc.push arg0)
        else
          -- Maybe we have a tuple: we simply return the current syntax
          trace[StepElab] "arg1 is not a comma"
          pure (acc.push stx)
      else if not isTuple then
        -- There should be an odd number of elements: element, comma, element, ...
        if args.size % 2 ≠ 1 then throwError "Expected an odd number of elements in comma separated syntax, got: {stx}"
        -- Check that the odd elements are commas
        let mut acc := acc
        for i in [0:args.size] do
          let arg := args[i]!
          if i % 2 = 0 then
            -- Should be an element
            acc := acc.push arg
          else
            -- Should be a comma
            match arg with
            | .atom _ "," => pure ()
            | _ => throwError "Expected a comma, got: {arg}"
        pure acc
      else throwError "Unsupported comma separated syntax: {stx}"

  /-- Given a pattern which decomposes a tuple or a struct (`(x, y, z)` or `⟨x, z, z⟩`, `((x, y), z, ⟨a, b⟩), etc.)`,
    return the list of identifiers appearing inside the pattern.

  Remark: I tried implementing something simpler based on pattern matching but couldn't get it to work. -/
  partial def getStepPurePatternIdents (stx : Syntax) : m (Array Ident) := do
    trace[StepElab] "syntax: {stx}"
    -- Check if this is an identifier
    match stx with
    | `(term| $name:ident) => pure #[name]
    |_ =>
    let args := stx.getArgs
    trace[StepElab] "args.size: {args.size}"

    -- Check if the syntax is `⟨ ... ⟩` or `( ... )`
    if args.size = 0 then throwError "Unsupported pattern syntax: empty syntax"
    if h: args.size = 3 then
      -- It should be a tuple: decompose it
      let arg0 := args[0]
      let arg1 := args[1]
      let arg2 := args[2]
      let (isTupleOrRecord, isTuple) :=
        match arg0, arg2 with
        | .atom _ "⟨", .atom _ "⟩" => (true, false)
        | .node _ _ #[.atom _ "(", _], .atom _ ")" => (true, true)
        | _, _ => (false, false)
      if not isTupleOrRecord then throwError "Unsupported pattern syntax: {stx}"
      let args ← parseCommaSeparated isTuple arg1
      trace[StepElab] "parsed args: {args}"
      -- Recursively decompose
      let xs ← args.mapM getStepPurePatternIdents
      -- Flatten
      pure xs.flatten
    else throwError "Unsupported pattern syntax: {stx}"

  open Lean Elab Command Term in
  /-- Command to check that we correctly parse tuples -/
  local elab "#check_elab_pattern" pat:term " as " ids:ident,* : command => do
    let ids' ← liftTermElabM (getStepPurePatternIdents pat)
    trace[StepElab] "Identifiers: {ids'.toList}"
    let ids ← ids.getElems.mapM fun x => do
      match x with
      | `(ident| $name:ident) => pure name
      | _ => throwError "not an identifier: {x}"
    if ids == ids' then
      trace[StepElab] "Success!"
    else
      throwError "Mismatch! Expected: {ids}, got: {ids'}"

  #check_elab_pattern ⟨⟩ as
  #check_elab_pattern () as
  #check_elab_pattern ⟨x⟩ as x
  #check_elab_pattern (x) as x
  #check_elab_pattern (x, y) as x, y
  #check_elab_pattern (x, y, z) as x, y, z
  #check_elab_pattern ((x, w), y, (a, b, c)) as x, w, y, a, b, c
  #check_elab_pattern (⟨x, w⟩, y, ⟨ a, b, c ⟩) as x, w, y, a, b, c
end

open Elab Term Attribute in
/-- We desugar patterns of the shape `foo = (x, y, z)` to `∃ x y z, foo = (x, y, z)` in order to bind
    the variables introduced in the right-hand side, allowing us to elaborate the patterns. -/
def elabStepPureAttribute (stx : Syntax) : AttrM (TSyntax `term) :=
  withRef stx do
    match stx with
    | `(attr| step_pure $x = $pat) => do
      let ids ← getStepPurePatternIdents pat
      let term ← ids.foldrM (fun id term => do
        `(term| ∃ $id:ident, $term)
        ) (← `(term| $x = $pat))
      pure term
    | `(attr| step_pure $pat) => do pure pat
    | _ => throwUnsupportedSyntax

/-- The step pure attribute -/
structure StepPureSpecAttr where
  attr : AttributeImpl
  deriving Inhabited

/-- The `step_pure` attribute lifts lemmas about pure functions to `step` lemmas.

   For instance, if we annotate the following theorem with `step_pure`:
   ```lean
   @[step_pure wrapping x y]
   theorem U32.wrapping_add_eq (x y : U32) :
    (wrapping_add x y).bv = x.bv + y.bv
   ```
   `step_pure` performs operations which are equivalent to introducing the following lemma:
   ```lean
   @[step]
   theorem U32.wrapping_add_eq.step_spec (x y : U32) :
    ↑(wrapping_add x y) ⦃ z => z.bv = x.bv + y.bv ⦄
   ```

   Note that it is possible to control how the output variable is decomposed in the generated lemma
   by writing an equality in the pattern we want to abstract over.
   For instance if we write:
   ```lean
   @[step_pure pos_pair = (x, y)]
   theorem pos_pair_is_pos : pos_pair.fst ≥ 0 ∧ pos_pair.snd ≥ 0
   ```
   we get:
   ```lean
   @[step]
   theorem pos_pair_is_pos.step_spec :
    ↑pos_pair ⦃ x y => x ≥ 0 ∧ y ≥ 0 ⦄
   ```

   Similarly if we write:
   ```lean
   @[step_pure pos_pair = z]
   theorem pos_pair_is_pos : pos_pair.fst ≥ 0 ∧ pos_pair.snd ≥ 0
   ```
   we get:
   ```lean
   @[step]
   theorem pos_pair_is_pos.step_spec :
    ↑pos_pair ⦃ z => z.fst ≥ 0 ∧ z.fst ≥ 0 ⦄
   ```

   If we don't put an equality in the pattern, `step_pure` will introduce one variable
   per field in the type of the pattern, if it is a tuple.
 -/
initialize stepPureAttribute : StepPureSpecAttr ← do
  let attrImpl : AttributeImpl := {
    name := `step_pure
    descr := "Adds lifted version of pure theorems to the `step_pure` database"
    add := fun thName stx attrKind => do
      -- Lookup the theorem
      let env ← getEnv
      -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
      attrIgnoreAuxDef thName (pure ()) do
        -- Elaborate the pattern
        let pat ← elabStepPureAttribute stx
        -- Introduce the lifted theorem
        let liftedThmName ← MetaM.run' (liftThm stx thName pat)
        -- Save the lifted theorem to the `step` database
        saveStepSpecFromThm stepAttr.ext attrKind stx liftedThmName
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl }

/-! # Attribute: `step_pure_def` -/

/-- Automatically generate a `step` theorem from a pure definition.

Example:
```lean
@[step_pure_def wrapping_add = (b, x)]
def wrapping_add (x y : U32) : Bool × U32 := ...
```
generates the theorem:
```lean
@[step]
theorem wrapping_add.step_spec (x y : U32) :
  (lift (wrapping_add x y)) ⦃ b x => (b, x) = wrapping_add x y ⦄
```
(note that the `z` appearing in the post-condition is eliminated when calling `step`,
leaving only `b` and `x` in the environment).
 -/
syntax (name := step_pure_def) "step_pure_def" (term)? : attr

/-- We desugar patterns of the shape `foo = (x, y, z)` to `∃ x y z, foo = (x, y, z)` in order to bind
    the variables introduced in the right-hand side, allowing us to elaborate the patterns. -/
def elabStepPureDefPattern (stx : Syntax) : AttrM (TSyntax `term) :=
  withRef stx do
    match stx with
    | `(term| $x = $pat)
    | `(term| ($x = $pat)) => do
      trace[StepElab] "elabStepPureDefPattern: equality pattern"
      let ids ← getStepPurePatternIdents pat
      let term ← ids.foldrM (fun id term => do
        `(term| ∃ $id:ident, $term)
        ) (← `(term| $x = $pat))
      pure term
    | `(term| $pat) => do
      trace[StepElab] "elabStepPureDefPattern: not an equality"
      pure pat

/-- The step pure def attribute -/
structure StepPureDefSpecAttr where
  attr : AttributeImpl
  deriving Inhabited

theorem specLiftDef {α} (x : α) :
    Std.WP.spec (Std.lift x) (Std.WP.successPost (fun y => y = x)) := by
  simp only [Std.lift, Std.WP.spec_ok, Std.WP.successPost_ok]

def mkStepPureDefThm (stx : Syntax) (pat : Option (TSyntax `term)) (n : Name)
  (suffix : String := "step_spec") : MetaM Name := do
  -- Regular case
  let mkPat (fvars : Array Expr) (ty : Expr) : MetaM Expr := do
    withTraceNode `Step (fun _ => pure m!"mkPat") do
    withLocalDeclD (← mkFreshUserName `x) ty fun v => do
    let x ← mkAppOptM n (fvars.map some)
    trace[Step] "x: {x}"
    let eq ← mkEq x v
    trace[Step] "eq: {eq}"
    let eq ← mkLambdaFVars #[v] eq
    let eq ← mkAppM ``Exists #[eq]
    trace[Step] "eq: {eq}"
    pure eq
  let mkPred (_ _ npat : Expr) (fvars : Array Expr) : MetaM Expr := do
    withTraceNode `Step (fun _ => pure m!"mkPred") do
    mkEq npat (← mkAppOptM n (fvars.map some))
  let tacticStx ←
    `(tactic|
        simp only
          [_root_.Aeneas.Std.lift, _root_.Aeneas.Std.WP.spec_ok,
           _root_.Aeneas.Std.WP.predn, _root_.Aeneas.Std.WP.successPost_ok,
           _root_.implies_true])
  liftThm stx n pat mkPat mkPred suffix (tacticStx := some tacticStx)

local elab "#step_pure_def" id:ident pat:(term)? : command => do
  Lean.Elab.Command.runTermElabM (fun _ => do
    let some cs ← Term.resolveId? id | throwError m!"Unknown id: {id}"
    let name := cs.constName!
    trace[StepElab] "pat: {pat}"
    let pat ← match pat with
      | some p => do pure (some (← elabStepPureDefPattern p))
      | none => pure none
    let _ ← mkStepPureDefThm id pat name
  )

namespace Test
  #step_pure_def overflowing_add
  #elab overflowing_add.step_spec

  /--
info: Aeneas.Step.Test.overflowing_add.step_spec (x y : U8) :
  Std.lift (overflowing_add x y) ⦃ x✝ => x✝ = overflowing_add x y ⦄
  -/
  #guard_msgs in
  #check overflowing_add.step_spec

  def wrapping_add (x y : U8) : U8 × Bool := (⟨ x.val + y.val ⟩, x.val + y.val ≥ 256)
  #step_pure_def wrapping_add (wrapping_add x y = (b, z))

  /--
info: Aeneas.Step.Test.wrapping_add.step_spec (x y : U8) : Std.lift (wrapping_add x y) ⦃ b z => (b, z) = wrapping_add x y ⦄
  -/
  #guard_msgs in
  #check wrapping_add.step_spec
end Test

def elabStepPureDefAttribute (stx : Syntax) : AttrM (Option (TSyntax `term)) :=
  withRef stx do
    match stx with
    | `(attr| step_pure_def $x = $pat)
    | `(attr| step_pure_def ($x = $pat)) => do
      trace[StepElab] "elabStepPureDefAttribute: equality pattern"
      let ids ← getStepPurePatternIdents pat
      let term ← ids.foldrM (fun id term => do
        `(term| ∃ $id:ident, $term)
        ) (← `(term| $x = $pat))
      pure (some term)
    | `(attr| step_pure_def $pat) => do
      trace[StepElab] "elabStepPureDefAttribute: not an equality"
      pure (some pat)
    | `(attr| step_pure_def) => do
      trace[StepElab] "elabStepPureDefAttribute: not an equality"
      pure none
    | _ => throwError "Unsupported syntax"

/- The `step_pure_def` attribute, which automatically generates
   step lemmas for pure definitions. -/
initialize stepPureDefAttribute : StepPureDefSpecAttr ← do
  let attrImpl : AttributeImpl := {
    name := `step_pure_def
    descr := "Automatically generate `step` theorems for pure definitions"
    add := fun declName stx attrKind => do
      -- Lookup the theorem
      let env ← getEnv
      -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
      attrIgnoreAuxDef declName (pure ()) do
      -- Elaborate the pattern
        trace[Saturate.attribute] "Syntax: {stx}"
        let pat ← elabStepPureDefAttribute stx
        -- Introduce the lifted theorem
        let thmName ← MetaM.run' (mkStepPureDefThm stx pat declName)
        -- Save the lifted theorem to the `step` database
        saveStepSpecFromThm stepAttr.ext attrKind stx thmName
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl }

open Tactic

/-! # Logging Utils -/
def traceGoalWithNode (msg : String) : TacticM Unit := Utils.traceGoalWithNode `Step msg

end Step


end Aeneas
