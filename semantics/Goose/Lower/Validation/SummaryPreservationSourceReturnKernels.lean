import Goose.Lower.Validation.SourceRootShapeReads
import Goose.Lower.Validation.SourceSymbolRefs
import Goose.Lower.Validation.SummaryPreservationSourceBlockContracts
import Goose.Lower.Validation.SummaryPreservationReplayControlTypedReturn
import Goose.Lower.Validation.SummaryPreservationSourceReturnScalarTyped

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem native_return_expression {vt : Array (Option VTy)} {loop : Option LoopCtx}
    {expression : Expr} {origin : OriginId} {le : LEnv} {initial : LS}
    (native : NativeRows vt (lowerStmt loop (.ret (some expression) origin) le initial).2) :
    NativeRows vt (lowerExpr expression le initial).2 := by
  let child := lowerExpr expression le initial
  let coerced := coerceResult child.1 origin le child.2
  let left := Goose.Lower.leaveTo 0 le coerced.2
  have whole : lowerStmt loop (.ret (some expression) origin) le initial =
      Goose.Lower.emitTerm (.ret [coerced.1] (some origin)) le left.2 := by
    simp only [lowerStmt, bind_run, child, coerced, left]
    rfl
  rw [whole] at native
  exact ((native.of_prefix (types_emitTerm _ le left.2 _ _ rfl)).of_prefix
    (types_leaveTo 0 le coerced.2 _ _ rfl)).of_prefix
      (types_coerceResult child.1 origin le child.2 _ _ rfl)

theorem statementReplay_return {typingEnv : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {loop : Option LoopCtx} {scope : ScopeId} {initial : LS} {upper : Prov}
    {expression : Expr} {origin : OriginId}
    (tables : SourceRootTables typingEnv env)
    (implementation : typingEnv.impl = some env.impl)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (checked : CtxOk env.mod env.impl env.ctx)
    (child : ExpressionReplayAt typingEnv env results vt target scopeCount expression initial upper) :
    StatementReplayAt typingEnv env results vt target scopeCount loop scope (.ret (some expression) origin)
      initial upper := by
  intro output start finish before after typed replay ceiling scopes stack ready generated loopBounds loopReplay native
  have originBound : origin < (lowerEnv env.mod env.impl.vars env.impl.results.toList).mod.origins.size := by
    simpa only [stmtSourceOrigin, lowerEnv, ← tables.moduleEq] using Core.tyStmt_success_origin_bound typed
  obtain ⟨expected, actual, impl, outside, implAt, resultTypes, expressionTyped, passable, _⟩ :=
    tyStmt_return_children typed
  have boundedStack := stack outside
  have childNative := native_return_expression native
  have childRun : ∀ actual roots value state,
      tyExpr typingEnv expression start = .ok (actual, finish) →
      rpExpr env expression before = .ok (roots, after) →
      lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial = (value, state) →
      EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
      ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
      ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
          (typedContextSlotUpper env.mod env.ctx env.impl) state next ∧
        (state.cur.isSome = true → ReplayValue (lowerContextAt env.mod env.ctx env.impl) next state value roots (.data actual)) ∧
        ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
    intro actual roots value state source replayed run effect input
    obtain ⟨next, nextReady, valueInfo, retained⟩ :=
      child actual start finish before after roots source replayed effect input generated childNative
    rw [run] at nextReady valueInfo
    exact ⟨next, nextReady, valueInfo, retained⟩
  by_cases refLike : (env.impl.results[0]?).any Ty.isRefLike = true
  · obtain ⟨next, returned, returnedState, coerced, whole, nextReady, candidate, retained⟩ :=
      ready.typedReturnValue loop typed replay ceiling ⟨rfl, rfl, rfl⟩ checked originBound boundedStack childRun
    refine ⟨next, nextReady, retained, ?_⟩
    intro declared declaredBounds prior
    apply prior.returned_expression loop ready.symbols ready.roots.valueSize generated expressionTyped rfl coerced retained
    intro live root member
    apply declaredBounds root
    simpa only [contextTypedResultUpper, implementationRow, refLike, ite_true,
      contextRefinedResultUpper] using candidate live root member
  · have nonref : (env.impl.results[0]?).any Ty.isRefLike = false := Bool.eq_false_iff.mpr refLike
    obtain ⟨next, returned, returnedState, coerced, whole, nextReady, scalar, retained⟩ :=
      ready.typedScalarReturn loop typed replay implementation nonref rfl ceiling originBound boundedStack childRun
    refine ⟨next, nextReady, retained, ?_⟩
    intro declared declaredBounds prior
    apply prior.returned_expression loop ready.symbols ready.roots.valueSize generated expressionTyped rfl coerced retained
    intro live root member
    rw [scalar live] at member
    cases member

#print axioms statementReplay_return

end Goose.Lower.Validation.SummaryPreservation
