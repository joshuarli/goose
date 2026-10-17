import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceContracts
import Goose.Lower.Validation.SummaryPreservationSourceBlockContracts
import Goose.Lower.Validation.SummaryPreservationSourceBoundContracts

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

def OccurrenceLoopCounterTyped (loop : Option LoopCtx) (types : Array (Option VTy)) : Prop :=
  match loop with
  | none => True
  | some context => match context.cont with
    | .jump _ => True
    | .next _ type counter => types[counter]? = some (some (.data (.int type)))

def BoundOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (bound : Bound) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.bound bound)) →
  ∀ start finish before after,
    Core.tyBound typingEnv bound start = .ok ((), finish) →
    rpBound env bound before = .ok ((), after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial
      (lowerContextAt env.mod env.ctx env.impl) vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial → NativeRows vt (lowerBound bound
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot (lowerContextAt env.mod env.ctx env.impl) (lowerBound bound
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl) (lowerBound bound
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerBound bound (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      ((lowerBound bound (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        ∀ value ∈ (lowerBound bound (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1.uses,
          value < (lowerBound bound (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.vals.size) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env (.bound bound) (lowerContextAt env.mod env.ctx env.impl) vt next initial
        (lowerBound bound (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerBound bound (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 (lowerContextAt env.mod env.ctx env.impl) vt next

def BlockOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (body : Core.Block) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.block body)) →
  ∀ type start finish before after sourceRoots range,
    Core.tyBlock typingEnv [] body start = .ok (type, finish) →
    rpBlockValue env [] body before = .ok ((sourceRoots, range), after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    SourceScopesWithin scopeCount (Core.blockScopes none body) →
    (∀ binding ∈ bindings, binding.1 < env.impl.vars.size ∧ binding.2.2 < env.mod.origins.size) →
    (initial.cur.isSome = true → ∀ binding ∈ bindings, binding.2.1 < initial.vals.size) →
    (∀ binding ∈ bindings, ∀ root ∈ rootsAt upper.vals binding.2.1,
      root ∈ rootsAt (typedContextSlotUpper env.mod env.ctx env.impl) binding.1) →
    (typingEnv.inExpr = false → ∀ entered ∈ initial.stack, entered < scopeCount) →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial
      (lowerContextAt env.mod env.ctx env.impl) vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial → LoopBuilderTargets loop initial →
    LoopReplayBounds loop scopeCount initial →
    OccurrenceLoopCounterTyped loop vt →
    ReplacementLoopTargetsIncluded loop siteTargets →
    NativeRows vt (lowerBlock loop bindings want body
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot (lowerContextAt env.mod env.ctx env.impl) (lowerBlock loop bindings want body
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl) (lowerBlock loop bindings want body
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      (want = true →
        (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        ReplayValue (lowerContextAt env.mod env.ctx env.impl) next
          (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2
          (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 sourceRoots (.data type)) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      (ReturnBoundsPreserved (contextTypedResultUpper env.mod env.ctx) initial upper
        (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next) ∧
      OccurrenceLedger env (.block body) (lowerContextAt env.mod env.ctx env.impl) vt next initial
        (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 (lowerContextAt env.mod env.ctx env.impl) vt next

def StatementOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId) (loop : Option LoopCtx)
    (scope : ScopeId) (statement : Stmt) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.statement statement)) →
  ∀ output start finish before after,
    Core.tyStmt typingEnv scope statement start = .ok (output, finish) →
    rpStmt env statement before = .ok ((), after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    SourceScopesWithin scopeCount (Core.stmtScopes none statement) →
    (typingEnv.inExpr = false → ∀ entered ∈ initial.stack, entered < scopeCount) →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial
      (lowerContextAt env.mod env.ctx env.impl) vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial → LoopBuilderTargets loop initial →
    LoopReplayBounds loop scopeCount initial →
    OccurrenceLoopCounterTyped loop vt →
    ReplacementLoopTargetsIncluded loop siteTargets →
    NativeRows vt (lowerStmt loop statement (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot (lowerContextAt env.mod env.ctx env.impl) (lowerStmt loop statement (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl) (lowerStmt loop statement (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerStmt loop statement (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      (ReturnBoundsPreserved (contextTypedResultUpper env.mod env.ctx) initial upper
        (lowerStmt loop statement (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next) ∧
      OccurrenceLedger env (.statement statement) (lowerContextAt env.mod env.ctx env.impl) vt next initial
        (lowerStmt loop statement (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerStmt loop statement (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 (lowerContextAt env.mod env.ctx env.impl) vt next

def StatementsOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId) (loop : Option LoopCtx)
    (root : DemandNode) (scope : ScopeId) (statements : List Stmt) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path root) →
  (∀ statement ∈ statements, ∃ path, DemandNodeAt root path (.statement statement)) →
  ∀ output start finish before after,
    Core.tyStmts typingEnv scope statements start = .ok (output, finish) →
    rpStmts env statements before = .ok ((), after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    SourceScopesWithin scopeCount (Core.stmtsScopes none statements) →
    (typingEnv.inExpr = false → ∀ entered ∈ initial.stack, entered < scopeCount) →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial
      (lowerContextAt env.mod env.ctx env.impl) vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial → LoopBuilderTargets loop initial →
    LoopReplayBounds loop scopeCount initial →
    OccurrenceLoopCounterTyped loop vt →
    ReplacementLoopTargetsIncluded loop siteTargets →
    NativeRows vt (lowerStmts loop statements (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot (lowerContextAt env.mod env.ctx env.impl) (lowerStmts loop statements (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl) (lowerStmts loop statements (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerStmts loop statements (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      (ReturnBoundsPreserved (contextTypedResultUpper env.mod env.ctx) initial upper
        (lowerStmts loop statements (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next) ∧
      OccurrenceLedger env (root) (lowerContextAt env.mod env.ctx env.impl) vt next initial
        (lowerStmts loop statements (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerStmts loop statements (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 (lowerContextAt env.mod env.ctx env.impl) vt next

end Goose.Lower.Validation.ReplacementContentFlowSource
