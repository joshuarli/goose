import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlContracts

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

def GlobalExpressionOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (expression : Expr) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.expression expression)) →
  ∀ type start finish before after sourceRoots,
    tyExpr typingEnv expression start = .ok (type, finish) →
    rpExpr env expression before = .ok (sourceRoots, after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars returnTypes) initial
      func vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial →
    NativeRows vt (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    NativeBuilderContinuation func (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      ((lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        ReplayValue func next
          (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2
          (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).1 sourceRoots (.data type)) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env (.expression expression)
        func vt next initial
        (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next

def GlobalPlaceOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (place : Place) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.place place)) →
  ∀ info start finish before after sourceRoots,
    tyPlace typingEnv place start = .ok (info, finish) →
    rpPlace env place before = .ok (sourceRoots, after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars returnTypes) initial
      func vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial →
    NativeRows vt (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    NativeBuilderContinuation func (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      ((lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).1 <
          (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).2.vals.size ∧
        GIR.RootsRefine func
          (rootsAt next.vals (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).1) sourceRoots) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env (.place place)
        func vt next initial
        (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next

def GlobalViewOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (view : View) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.view view)) →
  ∀ info start finish before after sourceRoots,
    tyView typingEnv view start = .ok (info, finish) →
    rpView env view before = .ok (sourceRoots, after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars returnTypes) initial
      func vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial →
    NativeRows vt (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    NativeBuilderContinuation func (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      ((lowerView view (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        ReplayValue func next
          (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) initial).2
          (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) initial).1 sourceRoots (.view .readOnly info.1)) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env (.view view)
        func vt next initial
        (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next


def GlobalBoundOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (bound : Bound) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.bound bound)) →
  ∀ start finish before after,
    Core.tyBound typingEnv bound start = .ok ((), finish) →
    rpBound env bound before = .ok ((), after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars returnTypes) initial
      func vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial → NativeRows vt (lowerBound bound
      (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func (lowerBound bound
      (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    NativeBuilderContinuation func (lowerBound bound
      (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerBound bound (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      ((lowerBound bound (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        ∀ value ∈ (lowerBound bound (lowerEnv env.mod env.impl.vars returnTypes) initial).1.uses,
          value < (lowerBound bound (lowerEnv env.mod env.impl.vars returnTypes) initial).2.vals.size) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env (.bound bound) func vt next initial
        (lowerBound bound (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerBound bound (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next

def GlobalBlockOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (body : Core.Block) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.block body)) →
  ∀ type start finish before after sourceRoots range,
    Core.tyBlock typingEnv [] body start = .ok (type, finish) →
    rpBlockValue env [] body before = .ok ((sourceRoots, range), after) →
    EffectRefinement func after.eff target →
    SourceScopesWithin scopeCount (Core.blockScopes none body) →
    (∀ binding ∈ bindings, binding.1 < env.impl.vars.size ∧ binding.2.2 < env.mod.origins.size) →
    (initial.cur.isSome = true → ∀ binding ∈ bindings, binding.2.1 < initial.vals.size) →
    (∀ binding ∈ bindings, ∀ root ∈ rootsAt upper.vals binding.2.1,
      root ∈ rootsAt slots binding.1) →
    (typingEnv.inExpr = false → ∀ entered ∈ initial.stack, entered < scopeCount) →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars returnTypes) initial
      func vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial → LoopBuilderTargets loop initial →
    LoopReplayBounds loop scopeCount initial →
    OccurrenceLoopCounterTyped loop vt →
    ReplacementLoopTargetsIncluded loop siteTargets →
    NativeRows vt (lowerBlock loop bindings want body
      (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func (lowerBlock loop bindings want body
      (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    NativeBuilderContinuation func (lowerBlock loop bindings want body
      (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      (want = true →
        (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        ReplayValue func next
          (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars returnTypes) initial).2
          (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars returnTypes) initial).1 sourceRoots (.data type)) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      (∀ expected, ReturnBoundsPreserved expected initial upper
        (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next) ∧
      OccurrenceLedger env (.block body) func vt next initial
        (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next

def GlobalStatementOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId) (loop : Option LoopCtx)
    (scope : ScopeId) (statement : Stmt) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.statement statement)) →
  ∀ output start finish before after,
    Core.tyStmt typingEnv scope statement start = .ok (output, finish) →
    rpStmt env statement before = .ok ((), after) →
    EffectRefinement func after.eff target →
    SourceScopesWithin scopeCount (Core.stmtScopes none statement) →
    (typingEnv.inExpr = false → ∀ entered ∈ initial.stack, entered < scopeCount) →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars returnTypes) initial
      func vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial → LoopBuilderTargets loop initial →
    LoopReplayBounds loop scopeCount initial →
    OccurrenceLoopCounterTyped loop vt →
    ReplacementLoopTargetsIncluded loop siteTargets →
    NativeRows vt (lowerStmt loop statement (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func (lowerStmt loop statement (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    NativeBuilderContinuation func (lowerStmt loop statement (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerStmt loop statement (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      (∀ expected, ReturnBoundsPreserved expected initial upper
        (lowerStmt loop statement (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next) ∧
      OccurrenceLedger env (.statement statement) func vt next initial
        (lowerStmt loop statement (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerStmt loop statement (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next

def GlobalStatementsOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId) (loop : Option LoopCtx)
    (root : DemandNode) (scope : ScopeId) (statements : List Stmt) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path root) →
  (∀ statement ∈ statements, ∃ path, DemandNodeAt root path (.statement statement)) →
  ∀ output start finish before after,
    Core.tyStmts typingEnv scope statements start = .ok (output, finish) →
    rpStmts env statements before = .ok ((), after) →
    EffectRefinement func after.eff target →
    SourceScopesWithin scopeCount (Core.stmtsScopes none statements) →
    (typingEnv.inExpr = false → ∀ entered ∈ initial.stack, entered < scopeCount) →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars returnTypes) initial
      func vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial → LoopBuilderTargets loop initial →
    LoopReplayBounds loop scopeCount initial →
    OccurrenceLoopCounterTyped loop vt →
    ReplacementLoopTargetsIncluded loop siteTargets →
    NativeRows vt (lowerStmts loop statements (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func (lowerStmts loop statements (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    NativeBuilderContinuation func (lowerStmts loop statements (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerStmts loop statements (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      (∀ expected, ReturnBoundsPreserved expected initial upper
        (lowerStmts loop statements (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next) ∧
      OccurrenceLedger env (root) func vt next initial
        (lowerStmts loop statements (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerStmts loop statements (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next


end Goose.Lower.Validation.ReplacementContentFlowSource
