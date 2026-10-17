import Goose.Lower.Validation.SourceCanonicalRootFloorsEnvironments
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlBlockValue
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts
import Goose.Lower.Validation.SummaryPreservationReplayTrackedNativeBlock

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

private theorem initialized_stack (scope : ScopeId) (bindings : List (SlotId × ValueId × OriginId))
    (le : LEnv) (initial : LS) :
    (initSlots bindings le (Goose.Lower.pushScope scope le
      (Goose.Lower.emitEffect (.enter scope) le initial).2).2).2.stack = scope :: initial.stack := by
  rw [(advB_initSlots bindings le _ _ _ rfl).stack]
  rw [pushScope_run]
  exact congrArg (List.cons scope) (advB_emitEffect (.enter scope) le initial _ _ rfl).stack

theorem globalBlockOccurrence_of_children {typingEnv : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
    {siteRoot : DemandNode} {siteTargets : List BlockId} {loop : Option LoopCtx} {bindings : List (SlotId × ValueId × OriginId)} {want : Bool}
    {scope : ScopeId} {statements : List Stmt} {value : Option Expr} {initial : LS} {upper : Prov}
    (inside : typingEnv.inExpr = true)
    (statementChild : ∀ nextEnv,
      nextEnv.mod = typingEnv.mod → nextEnv.vars = typingEnv.vars →
      nextEnv.impl = typingEnv.impl → nextEnv.inExpr = typingEnv.inExpr → ∀ state provenance,
      GlobalStatementsOccurrenceReplayAt nextEnv { env with scopes := scope :: env.scopes } results vt func returnTypes slots target scopeCount
        siteRoot siteTargets loop (.block (.mk scope statements value)) scope statements state provenance)
    (expressionChild : ∀ expression, value = some expression →
      SourceScopesWithin scopeCount (Core.exprScopes none expression) → ∀ nextEnv,
      nextEnv.mod = typingEnv.mod → nextEnv.vars = typingEnv.vars →
      nextEnv.impl = typingEnv.impl → nextEnv.inExpr = typingEnv.inExpr → ∀ state provenance,
      GlobalExpressionOccurrenceReplayAt nextEnv { env with scopes := scope :: env.scopes } results vt func returnTypes slots target scopeCount
        siteRoot siteTargets expression state provenance) :
    GlobalBlockOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets loop bindings want
      (.mk scope statements value) initial upper := by
  intro source type start finish before after roots range typed replay ceiling scopes metadata values rootBounds stack ready sites targetBounds generated loopBounds loopReplay counterTyped included native projects continuation
  have assembled : ∃ next,
      ReplayBuilder (lower env.mod) results vt func target (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots
        (lowerBlock loop bindings want (.mk scope statements value) (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      (want = true → (lowerBlock loop bindings want (.mk scope statements value) (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        ReplayValue func next (lowerBlock loop bindings want (.mk scope statements value) (lowerEnv env.mod env.impl.vars returnTypes) initial).2
          (lowerBlock loop bindings want (.mk scope statements value) (lowerEnv env.mod env.impl.vars returnTypes) initial).1 roots (.data type)) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved [] initial upper
        (lowerBlock loop bindings want (.mk scope statements value) (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      OccurrenceLedger env (.block (.mk scope statements value)) func vt next initial
        (lowerBlock loop bindings want (.mk scope statements value) (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerBlock loop bindings want (.mk scope statements value) (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next := by
    have parts := SourceScopesWithin.block_parts scopes
    have statementScopes := (SourceScopesWithin.statements_parent statements (some scope) none).mp parts.2.1
    let le := lowerEnv env.mod env.impl.vars returnTypes
    obtain ⟨_, env1, tn1, env2, tn2, declared, typedStatements, typedValue⟩ :=
      tyBlock_ok typingEnv [] scope statements value start type finish typed
    obtain ⟨_, sourceMiddle, rootStatements, rootValue, _localRoots, _range⟩ :=
      rpBlockValue_ok env [] scope statements value before roots range after replay
    have declaredSame := (declarePre_ok _ _ _ _ _ _ declared).1
    have declaredTables := declarePre_tables [] declared
    have statementTables := tyStmts_tables statements typedStatements
    have statementEffect : EffectRefinement func sourceMiddle.eff target := by
      cases value with
      | none => simpa only [rootValue.2] using ceiling
      | some expression => exact effectRefinement_before_expression rootValue ceiling
    apply blockOccurrenceAction (env := env) (root := .block (.mk scope statements value))
      loop bindings want scope statements value roots (.data type) ([] : List RootRef)
      ready sites targetBounds parts.1
      (by intro binding member; exact ⟨by simpa only [lowerEnv, Array.size_mapIdx] using (metadata binding member).1,
        (metadata binding member).2⟩)
      values (by intro binding member root memberRoot; rw [ready.slotsEq]; exact rootBounds binding member root memberRoot) projects continuation
    · intro state provenance entryEq stateReady stateSites stateBounds childProjects childContinuation
      obtain ⟨initializedGenerated, _bodyGenerated, bodyNative, _valueNative⟩ := native_block_stages generated loopBounds native
      have childGenerated : GeneratedBuilderState state := by rw [entryEq]; exact initializedGenerated
      have childNative : NativeRows vt (lowerStmts loop statements le state).2 := by rw [entryEq]; exact bodyNative
      have childStack : env1.inExpr = false → ∀ entered ∈ state.stack, entered < scopeCount := by
        intro outside entered member
        rw [entryEq, initialized_stack] at member
        rcases List.mem_cons.mp member with rfl | retained
        · exact parts.1
        · exact stack (declaredSame.inExpr.symm.trans outside) entered retained
      have childLoop := loopBounds.mono (show initial.blocks.size ≤ state.blocks.size by
        rw [entryEq]
        exact Nat.le_trans (advB_emitEffect (.enter scope) le initial _ _ rfl).ext.1
          (by simpa only [le, pushScope_run, Goose.Lower.emitEffect, Goose.Lower.curBlock, bind_run, get_apply, pure_run] using (advB_initSlots bindings le
            (Goose.Lower.pushScope scope le (Goose.Lower.emitEffect (.enter scope) le initial).2).2 _ _ rfl).ext.1))
      have childLoopReplay : LoopReplayBounds loop scopeCount state := by
        rw [entryEq]
        exact ((loopReplay.mono (advB_emitEffect (.enter scope) _ initial _ _ rfl)).pushScope parts.1).mono
          (advB_initSlots bindings _ _ _ _ rfl)
      have origins : ∀ statement ∈ statements,
          ∃ path, DemandNodeAt (.block (.mk scope statements value)) path (.statement statement) := by
        intro statement member
        obtain ⟨index, row⟩ := List.mem_iff_getElem?.mp member
        refine ⟨[index], .child ?_ (.here _)⟩
        simp only [DemandNode.child?, DemandNode.children, List.getElem?_append, List.getElem?_map]
        have bounded : index < statements.length := (List.getElem?_eq_some_iff.mp row).1
        simpa [bounded] using (List.getElem?_eq_some_iff.mp row).2
      obtain ⟨next, completed, retained, returns, ledger, finalSites⟩ :=
        statementChild env1 declaredTables.1 declaredTables.2.1 declaredSame.impl declaredSame.inExpr
          state provenance source origins env2 tn1 tn2 _ sourceMiddle typedStatements rootStatements statementEffect
          statementScopes childStack stateReady (stateSites.access_eq rfl) stateBounds childGenerated
          childLoop childLoopReplay counterTyped included childNative (SourceCanonicalRootFloors.RecipeMetadataProjects.access (left := env) (right := { env with scopes := scope :: env.scopes }) rfl childProjects) childContinuation
      exact ⟨next, completed, retained, returns [], OccurrenceLedger.access_eq (env := { env with scopes := scope :: env.scopes }) (nextEnv := env) rfl ledger, finalSites.access_eq rfl⟩
    · intro state provenance entryEq stateReady stateSites stateBounds childProjects childContinuation
      obtain ⟨_initializedGenerated, bodyGenerated, _bodyNative, valueNative⟩ := native_block_stages generated loopBounds native
      have childGenerated : GeneratedBuilderState state := by rw [entryEq]; exact bodyGenerated
      have childNative : NativeRows vt (lowerBlockValue want value le state).2 := by rw [entryEq]; exact valueNative
      have valueFree : ReturnFreeValue value := by
        cases value with
        | none => trivial
        | some expression => exact tyExpr_returnFree expression typedValue
      apply blockOccurrenceValue want value roots (.data type) stateReady stateSites
        (by intro absent; subst value; exact ⟨rootValue.1, congrArg VTy.data typedValue.1⟩) valueFree
      intro expression present
      subst value
      have expressionScopes : SourceScopesWithin scopeCount (Core.exprScopes none expression) := by
        apply (SourceScopesWithin.expression_parent expression (some scope) none).mp
        exact parts.2.2
      have expressionAt : DemandNodeAt (.block (.mk scope statements (some expression))) [statements.length] (.expression expression) := by
        refine .child ?_ (.here _)
        simp [DemandNode.child?, DemandNode.children]
      have expressionSource : ∃ path, DemandNodeAt siteRoot path (.expression expression) := by
        obtain ⟨path, location⟩ := source
        exact ⟨path ++ [statements.length], sourcePath_append location expressionAt⟩
      obtain ⟨next, completed, returned, retained, ledger, finalSites⟩ :=
        expressionChild expression rfl expressionScopes env2
          (statementTables.1.trans declaredTables.1) (statementTables.2.1.trans declaredTables.2.1)
          (statementTables.2.2.trans declaredSame.impl)
          ((source_statements_inExpr statements typedStatements).trans declaredSame.inExpr)
          state provenance expressionSource type tn2 finish sourceMiddle after roots
          typedValue rootValue ceiling
          stateReady (stateSites.access_eq rfl) stateBounds childGenerated
          (by simpa only [lowerBlockValue] using childNative)
        (by simpa only [lowerBlockValue] using SourceCanonicalRootFloors.RecipeMetadataProjects.access (left := env) (right := { env with scopes := scope :: env.scopes }) rfl childProjects)
        (by simpa only [lowerBlockValue] using childContinuation)
      exact ⟨next, completed, returned, retained, OccurrenceLedger.access_eq (env := { env with scopes := scope :: env.scopes }) (nextEnv := env) rfl (ledger.underRoot expressionAt), finalSites.access_eq rfl⟩
  obtain ⟨next, completed, returned, retained, _, ledger, finalSites⟩ := assembled
  refine ⟨next, completed, returned, retained, ?_, ledger, finalSites⟩
  intro expected
  exact ReturnBoundsPreserved.frame ready.symbols ready.roots.valueSize retained
    (returnFrame_lowerBlock loop bindings want (.mk scope statements value)
      (tyBlock_returnFree _ [] typed inside) _ _ _ _ rfl)

#print axioms globalBlockOccurrence_of_children

end Goose.Lower.Validation.ReplacementContentFlowSource
