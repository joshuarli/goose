import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalSites

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource

def CanonicalChildrenAt (ownerRoot : Fragment) (le : LEnv) (ownerInitial : LS) (children : List Child) : Prop :=
  ∀ child before, some (child,before) ∈ children →
    ∃ path, SourceLoweringAt ownerRoot le ownerInitial path child before

theorem SourceLoweringAt.childrenAt {ownerRoot fragment : Fragment} {le : LEnv} {ownerInitial before : LS}
    {path : List Nat} (located : SourceLoweringAt ownerRoot le ownerInitial path fragment before) :
    CanonicalChildrenAt ownerRoot le ownerInitial (fragment.children le before) := by
  intro child start member
  obtain ⟨index,row⟩ := List.mem_iff_getElem?.mp member
  refine ⟨path ++ [index],located.child ?_⟩
  simp only [Fragment.child?,row,Option.join_some]

def CanonicalGlobalExpressionOccurrenceReplayAt (ownerRoot : Fragment) (ownerInitial baseline : LS) (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (expression : Expr) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.expression expression)) →
  (∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars returnTypes) ownerInitial path (.expression expression) initial) →
  ∀ type start finish before after sourceRoots,
    tyExpr typingEnv expression start = .ok (type, finish) →
    rpExpr env expression before = .ok (sourceRoots, after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
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
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next

def CanonicalGlobalPlaceOccurrenceReplayAt (ownerRoot : Fragment) (ownerInitial baseline : LS) (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (place : Place) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.place place)) →
  (∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars returnTypes) ownerInitial path (.place place) initial) →
  ∀ info start finish before after sourceRoots,
    tyPlace typingEnv place start = .ok (info, finish) →
    rpPlace env place before = .ok (sourceRoots, after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
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
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next

def CanonicalGlobalViewOccurrenceReplayAt (ownerRoot : Fragment) (ownerInitial baseline : LS) (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (view : View) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.view view)) →
  (∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars returnTypes) ownerInitial path (.view view) initial) →
  ∀ info start finish before after sourceRoots,
    tyView typingEnv view start = .ok (info, finish) →
    rpView env view before = .ok (sourceRoots, after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
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
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next


def CanonicalGlobalBoundOccurrenceReplayAt (ownerRoot : Fragment) (ownerInitial baseline : LS) (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (bound : Bound) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.bound bound)) →
  (∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars returnTypes) ownerInitial path (.bound bound) initial) →
  ∀ start finish before after,
    Core.tyBound typingEnv bound start = .ok ((), finish) →
    rpBound env bound before = .ok ((), after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
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
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerBound bound (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next

def CanonicalGlobalBlockOccurrenceReplayAt (ownerRoot : Fragment) (ownerInitial baseline : LS) (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (body : Core.Block) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.block body)) →
  (∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars returnTypes) ownerInitial path (.block loop bindings want body) initial) →
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
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
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
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next

def CanonicalGlobalStatementOccurrenceReplayAt (ownerRoot : Fragment) (ownerInitial baseline : LS) (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId) (loop : Option LoopCtx)
    (scope : ScopeId) (statement : Stmt) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.statement statement)) →
  (∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars returnTypes) ownerInitial path (.statement loop statement) initial) →
  ∀ output start finish before after,
    Core.tyStmt typingEnv scope statement start = .ok (output, finish) →
    rpStmt env statement before = .ok ((), after) →
    EffectRefinement func after.eff target →
    SourceScopesWithin scopeCount (Core.stmtScopes none statement) →
    (typingEnv.inExpr = false → ∀ entered ∈ initial.stack, entered < scopeCount) →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
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
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerStmt loop statement (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next

def CanonicalGlobalStatementsOccurrenceReplayAt (ownerRoot : Fragment) (ownerInitial baseline : LS) (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId) (loop : Option LoopCtx)
    (root : DemandNode) (scope : ScopeId) (statements : List Stmt) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path root) →
  (∀ statement ∈ statements, ∃ path, DemandNodeAt root path (.statement statement)) →
  CanonicalChildrenAt ownerRoot (lowerEnv env.mod env.impl.vars returnTypes) ownerInitial
    (statementChildren (lowerEnv env.mod env.impl.vars returnTypes) loop statements initial) →
  ∀ output start finish before after,
    Core.tyStmts typingEnv scope statements start = .ok (output, finish) →
    rpStmts env statements before = .ok ((), after) →
    EffectRefinement func after.eff target →
    SourceScopesWithin scopeCount (Core.stmtsScopes none statements) →
    (typingEnv.inExpr = false → ∀ entered ∈ initial.stack, entered < scopeCount) →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
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
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerStmts loop statements (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next


def CanonicalExpressionOccurrenceReplayAt (ownerRoot : Fragment) (ownerInitial baseline : LS) (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (expression : Expr) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.expression expression)) →
  (∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars env.impl.results.toList) ownerInitial path (.expression expression) initial) →
  ∀ type start finish before after sourceRoots,
    tyExpr typingEnv expression start = .ok (type, finish) →
    rpExpr env expression before = .ok (sourceRoots, after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial
      (lowerContextAt env.mod env.ctx env.impl) vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial →
    NativeRows vt (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot (lowerContextAt env.mod env.ctx env.impl) (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl) (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      ((lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        ReplayValue (lowerContextAt env.mod env.ctx env.impl) next
          (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2
          (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 sourceRoots (.data type)) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env (.expression expression)
        (lowerContextAt env.mod env.ctx env.impl) vt next initial
        (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 (lowerContextAt env.mod env.ctx env.impl) vt next

def CanonicalPlaceOccurrenceReplayAt (ownerRoot : Fragment) (ownerInitial baseline : LS) (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (place : Place) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.place place)) →
  (∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars env.impl.results.toList) ownerInitial path (.place place) initial) →
  ∀ info start finish before after sourceRoots,
    tyPlace typingEnv place start = .ok (info, finish) →
    rpPlace env place before = .ok (sourceRoots, after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial
      (lowerContextAt env.mod env.ctx env.impl) vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial →
    NativeRows vt (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot (lowerContextAt env.mod env.ctx env.impl) (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl) (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      ((lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 <
          (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.vals.size ∧
        GIR.RootsRefine (lowerContextAt env.mod env.ctx env.impl)
          (rootsAt next.vals (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1) sourceRoots) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env (.place place)
        (lowerContextAt env.mod env.ctx env.impl) vt next initial
        (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 (lowerContextAt env.mod env.ctx env.impl) vt next

def CanonicalViewOccurrenceReplayAt (ownerRoot : Fragment) (ownerInitial baseline : LS) (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (view : View) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.view view)) →
  (∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars env.impl.results.toList) ownerInitial path (.view view) initial) →
  ∀ info start finish before after sourceRoots,
    tyView typingEnv view start = .ok (info, finish) →
    rpView env view before = .ok (sourceRoots, after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial
      (lowerContextAt env.mod env.ctx env.impl) vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial →
    NativeRows vt (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot (lowerContextAt env.mod env.ctx env.impl) (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl) (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      ((lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        ReplayValue (lowerContextAt env.mod env.ctx env.impl) next
          (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2
          (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 sourceRoots (.view .readOnly info.1)) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env (.view view)
        (lowerContextAt env.mod env.ctx env.impl) vt next initial
        (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 (lowerContextAt env.mod env.ctx env.impl) vt next

def CanonicalBoundOccurrenceReplayAt (ownerRoot : Fragment) (ownerInitial baseline : LS) (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (bound : Bound) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.bound bound)) →
  (∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars env.impl.results.toList) ownerInitial path (.bound bound) initial) →
  ∀ start finish before after,
    Core.tyBound typingEnv bound start = .ok ((), finish) →
    rpBound env bound before = .ok ((), after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
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
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerBound bound (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 (lowerContextAt env.mod env.ctx env.impl) vt next

def CanonicalBlockOccurrenceReplayAt (ownerRoot : Fragment) (ownerInitial baseline : LS) (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (body : Core.Block) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.block body)) →
  (∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars env.impl.results.toList) ownerInitial path (.block loop bindings want body) initial) →
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
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
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
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 (lowerContextAt env.mod env.ctx env.impl) vt next

def CanonicalStatementOccurrenceReplayAt (ownerRoot : Fragment) (ownerInitial baseline : LS) (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId) (loop : Option LoopCtx)
    (scope : ScopeId) (statement : Stmt) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.statement statement)) →
  (∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars env.impl.results.toList) ownerInitial path (.statement loop statement) initial) →
  ∀ output start finish before after,
    Core.tyStmt typingEnv scope statement start = .ok (output, finish) →
    rpStmt env statement before = .ok ((), after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    SourceScopesWithin scopeCount (Core.stmtScopes none statement) →
    (typingEnv.inExpr = false → ∀ entered ∈ initial.stack, entered < scopeCount) →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
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
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerStmt loop statement (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 (lowerContextAt env.mod env.ctx env.impl) vt next

def CanonicalStatementsOccurrenceReplayAt (ownerRoot : Fragment) (ownerInitial baseline : LS) (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId) (loop : Option LoopCtx)
    (root : DemandNode) (scope : ScopeId) (statements : List Stmt) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path root) →
  (∀ statement ∈ statements, ∃ path, DemandNodeAt root path (.statement statement)) →
  CanonicalChildrenAt ownerRoot (lowerEnv env.mod env.impl.vars env.impl.results.toList) ownerInitial
    (statementChildren (lowerEnv env.mod env.impl.vars env.impl.results.toList) loop statements initial) →
  ∀ output start finish before after,
    Core.tyStmts typingEnv scope statements start = .ok (output, finish) →
    rpStmts env statements before = .ok ((), after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    SourceScopesWithin scopeCount (Core.stmtsScopes none statements) →
    (typingEnv.inExpr = false → ∀ entered ∈ initial.stack, entered < scopeCount) →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
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
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerStmts loop statements (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 (lowerContextAt env.mod env.ctx env.impl) vt next

end Goose.Lower.Validation.SourceReplacementWriterLedger
