import Goose.Lower.Validation.SummaryPreservationReplayBlock
import Goose.Lower.Validation.SummaryPreservationSourceEffectCeiling
import Goose.Core.Sound.Invert
import Goose.Lower.Validation.SourceEnvironment

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedBlock {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
    {env : TEnv} {penv : PEnv} {typedPre : List (VarId × Ty)} {rootPre : List VarId}
    {start finish : Nat} {type : Ty} {before after : RState} {range : Nat × Nat}
    {sourceRoots : List RootRef} (loop : Option LoopCtx)
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
    (statementChild : ∀ env1 env2 tn1 tn2 sourceBefore sourceAfter state provenance,
      env1.mod = env.mod → env1.vars = env.vars →
      tyStmts env1 scope statements tn1 = .ok (env2, tn2) →
      rpStmts { penv with scopes := scope :: penv.scopes } statements sourceBefore = .ok ((), sourceAfter) →
      EffectRefinement func sourceAfter.eff target →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerStmts loop statements le state).2 next ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    (expressionChild : ∀ expression env2 tn2 sourceBefore state provenance,
      env2.mod = env.mod → env2.vars = env.vars →
      value = some expression → tyExpr env2 expression tn2 = .ok (type, finish) →
      rpExpr { penv with scopes := scope :: penv.scopes } expression sourceBefore = .ok (sourceRoots, after) →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
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
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨_, env1, tn1, env2, tn2, declared, typedStatements, typedValue⟩ :=
    tyBlock_ok env typedPre scope statements value start type finish source
  obtain ⟨_, sourceMiddle, rootStatements, rootValue, _localRoots, _range⟩ :=
    rpBlockValue_ok penv rootPre scope statements value before sourceRoots range after replayed
  have declaredTables := declarePre_tables typedPre declared
  have statementTables := tyStmts_tables statements typedStatements
  have statementEffect : EffectRefinement func sourceMiddle.eff target := by
    cases value with
    | none => simpa only [rootValue.2] using wholeEffect
    | some expression => exact effectRefinement_before_expression rootValue wholeEffect
  apply ready.blockAction loop bindings want scope statements value sourceRoots (.data type)
    scopeBound metadata values roots
  · intro state provenance _entry stateReady
    exact statementChild env1 env2 tn1 tn2 _ sourceMiddle state provenance
      declaredTables.1 declaredTables.2.1 typedStatements rootStatements statementEffect stateReady
  · intro state provenance _entry stateReady
    apply stateReady.blockValue want value sourceRoots (.data type)
    · intro absent
      subst value
      exact ⟨rootValue.1, congrArg VTy.data typedValue.1⟩
    · intro expression present
      subst value
      exact expressionChild expression env2 tn2 sourceMiddle state provenance
        (statementTables.1.trans declaredTables.1) (statementTables.2.1.trans declaredTables.2.1)
        rfl typedValue rootValue stateReady

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
