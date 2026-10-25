import Goose.Lower.Validation.SummaryPreservationSourceEnvironments
import Goose.Lower.Validation.SummaryPreservationReplayNativeBlock
import Goose.Lower.Validation.SummaryPreservationReplayTrackedBlock

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedBlockTrackedNative {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
    {env : TEnv} {penv : PEnv} {typedPre : List (VarId × Ty)} {rootPre : List VarId}
    {start finish : Nat} {type : Ty} {before after : RState} {range : Nat × Nat}
    {sourceRoots : List RootRef} (loop : Option LoopCtx) (expected : List RootRef)
    (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (scope : ScopeId) (statements : List Stmt) (value : Option Expr)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : tyBlock env typedPre (.mk scope statements value) start = .ok (type, finish))
    (replayed : rpBlockValue penv rootPre (.mk scope statements value) before = .ok ((sourceRoots, range), after))
    (wholeEffect : EffectRefinement func after.eff target)
    (scopeBound : scope < scopeCount)
    (metadata : ∀ binding ∈ bindings,
      binding.1 < le.slots.size ∧ binding.2.2 < le.mod.origins.size)
    (values : ls.cur.isSome = true → ∀ binding ∈ bindings, binding.2.1 < ls.vals.size)
    (roots : ∀ binding ∈ bindings, ∀ root ∈ rootsAt upper.vals binding.2.1,
      root ∈ rootsAt upper.slots binding.1)
    (generated : GeneratedBuilderState ls)
    (loopBounds : LoopBuilderTargets loop ls)
    (native : NativeRows vt (lowerBlock loop bindings want (.mk scope statements value) le ls).2)
    (statementChild : ∀ env1 env2 tn1 tn2 sourceBefore sourceAfter state provenance,
      env1.mod = env.mod → env1.vars = env.vars → env1.impl = env.impl → env1.inExpr = env.inExpr →
      tyStmts env1 scope statements tn1 = .ok (env2, tn2) →
      rpStmts { penv with scopes := scope :: penv.scopes } statements sourceBefore = .ok ((), sourceAfter) →
      EffectRefinement func sourceAfter.eff target →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      state = (initSlots bindings le (Goose.Lower.pushScope scope le
        (Goose.Lower.emitEffect (.enter scope) le ls).2).2).2 →
      GeneratedBuilderState state → NativeRows vt (lowerStmts loop statements le state).2 →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerStmts loop statements le state).2 next ∧
        (∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) ∧
        ReturnBoundsPreserved expected state provenance (lowerStmts loop statements le state).2 next)
    (expressionChild : ∀ expression env2 tn2 sourceBefore state provenance,
      env2.mod = env.mod → env2.vars = env.vars → env2.impl = env.impl → env2.inExpr = env.inExpr →
      value = some expression → tyExpr env2 expression tn2 = .ok (type, finish) →
      rpExpr { penv with scopes := scope :: penv.scopes } expression sourceBefore = .ok (sourceRoots, after) →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      state = (lowerStmts loop statements le (initSlots bindings le (Goose.Lower.pushScope scope le
        (Goose.Lower.emitEffect (.enter scope) le ls).2).2).2).2 →
      GeneratedBuilderState state → NativeRows vt (lowerExpr expression le state).2 →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerExpr expression le state).2 next ∧
        ((lowerExpr expression le state).2.cur.isSome = true →
          ReplayValue func next (lowerExpr expression le state).2
            (lowerExpr expression le state).1 sourceRoots (.data type)) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerBlock loop bindings want (.mk scope statements value) le ls).2 next ∧
      (want = true → (lowerBlock loop bindings want (.mk scope statements value) le ls).2.cur.isSome = true →
        ReplayValue func next (lowerBlock loop bindings want (.mk scope statements value) le ls).2
          (lowerBlock loop bindings want (.mk scope statements value) le ls).1 sourceRoots (.data type)) ∧
      (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
      ReturnBoundsPreserved expected ls upper
        (lowerBlock loop bindings want (.mk scope statements value) le ls).2 next := by
  obtain ⟨_, env1, tn1, env2, tn2, declared, typedStatements, typedValue⟩ :=
    tyBlock_ok env typedPre scope statements value start type finish source
  obtain ⟨_, sourceMiddle, rootStatements, rootValue, _localRoots, _range⟩ :=
    rpBlockValue_ok penv rootPre scope statements value before sourceRoots range after replayed
  have declaredSame := (declarePre_ok _ _ _ _ _ _ declared).1
  have declaredTables := declarePre_tables typedPre declared
  have statementTables := tyStmts_tables statements typedStatements
  have statementEffect : EffectRefinement func sourceMiddle.eff target := by
    cases value with
    | none => simpa only [rootValue.2] using wholeEffect
    | some expression => exact effectRefinement_before_expression rootValue wholeEffect
  apply ready.blockActionTracked loop bindings want scope statements value sourceRoots (.data type) expected
    scopeBound metadata values roots
  · intro state provenance entryEq stateReady
    obtain ⟨initializedGenerated, _bodyGenerated, bodyNative, _valueNative⟩ := native_block_stages generated loopBounds native
    have childGenerated : GeneratedBuilderState state := by rw [entryEq]; exact initializedGenerated
    have childNative : NativeRows vt (lowerStmts loop statements le state).2 := by rw [entryEq]; exact bodyNative
    exact statementChild env1 env2 tn1 tn2 _ sourceMiddle state provenance
      declaredTables.1 declaredTables.2.1 declaredSame.impl declaredSame.inExpr typedStatements rootStatements statementEffect stateReady entryEq childGenerated childNative
  · intro state provenance entryEq stateReady
    obtain ⟨_initializedGenerated, bodyGenerated, _bodyNative, valueNative⟩ := native_block_stages generated loopBounds native
    have childGenerated : GeneratedBuilderState state := by rw [entryEq]; exact bodyGenerated
    have childNative : NativeRows vt (lowerBlockValue want value le state).2 := by rw [entryEq]; exact valueNative
    have valueFree : ReturnFreeValue value := by
      cases value with
      | none => trivial
      | some expression => exact tyExpr_returnFree expression typedValue
    obtain ⟨next, nextReady, returned, retained⟩ := stateReady.blockValue want value sourceRoots (.data type)
      (by
        intro absent
        subst value
        exact ⟨rootValue.1, congrArg VTy.data typedValue.1⟩)
      (by
        intro expression present
        subst value
        exact expressionChild expression env2 tn2 sourceMiddle state provenance
          (statementTables.1.trans declaredTables.1) (statementTables.2.1.trans declaredTables.2.1)
          (statementTables.2.2.trans declaredSame.impl)
          ((source_statements_inExpr statements typedStatements).trans declaredSame.inExpr)
          rfl typedValue rootValue stateReady entryEq childGenerated childNative)
    have frame := ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_lowerBlockValue want value valueFree)
      le state (lowerBlockValue want value le state).1 (lowerBlockValue want value le state).2 rfl
    exact ⟨next, nextReady, returned, retained,
      ReturnBoundsPreserved.frame stateReady.symbols stateReady.roots.valueSize retained frame⟩

#print axioms typedBlockTrackedNative

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
