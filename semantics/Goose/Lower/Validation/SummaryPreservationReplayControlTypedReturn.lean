import Goose.Lower.Validation.SummaryPreservationReplayControlReturns

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedReturnValue {module : GIR.Module} {sourceModule : Core.Module} {ctx : Context} {impl : Impl}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
    {env output : TEnv} {penv : PEnv} {expression : Expr} {origin : OriginId}
    {scope start finish : Nat} {before after : RState} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt (lowerContextAt sourceModule ctx impl)
      target le scopeCount slots ls upper)
    (source : tyStmt env scope (.ret (some expression) origin) start = .ok (output, finish))
    (replayed : rpStmt penv (.ret (some expression) origin) before = .ok ((), after))
    (wholeEffect : EffectRefinement (lowerContextAt sourceModule ctx impl) after.eff target)
    (sourceContext : penv.mod = sourceModule ∧ penv.ctx = ctx ∧ penv.impl = impl)
    (contextOk : CtxOk penv.mod penv.impl penv.ctx)
    (originBound : origin < le.mod.origins.size)
    (scopes : ∀ scope ∈ ls.stack, scope < scopeCount)
    (child : ∀ actual roots value state,
      tyExpr env expression start = .ok (actual, finish) →
      rpExpr penv expression before = .ok (roots, after) →
      lowerExpr expression le ls = (value, state) →
      EffectRefinement (lowerContextAt sourceModule ctx impl) after.eff target →
      ReplayBuilder module results vt (lowerContextAt sourceModule ctx impl)
        target le scopeCount slots ls upper →
      ∃ next, ReplayBuilder module results vt (lowerContextAt sourceModule ctx impl)
          target le scopeCount slots state next ∧
        (state.cur.isSome = true → ReplayValue (lowerContextAt sourceModule ctx impl) next state value roots (.data actual)) ∧
        ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) :
    ∃ next returned returnedState,
      Goose.Lower.coerceResult (lowerExpr expression le ls).1 origin le (lowerExpr expression le ls).2 =
        (returned, returnedState) ∧
      lowerStmt loop (.ret (some expression) origin) le ls =
        Goose.Lower.emitTerm (.ret [returned] (some origin)) le (Goose.Lower.leaveTo 0 le returnedState).2 ∧
      ReplayBuilder module results vt (lowerContextAt sourceModule ctx impl)
        target le scopeCount slots (lowerStmt loop (.ret (some expression) origin) le ls).2 next ∧
      (returnedState.cur.isSome = true →
        ∀ root ∈ rootsAt next.vals returned,
          root ∈ refinedResultUpper (lowerContextAt sourceModule ctx impl) (ctx.resultRoots[0]?.getD [])) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨expected, actual, typedImpl, _, _, _, typed, _, _⟩ := tyStmt_return_children source
  obtain ⟨roots, middle, expressionReplay, checking⟩ := (st_bind_ok _ _ _ _).mp replayed
  have checked := (liftV_ok _ _ _).mp checking
  have same : after = middle := checked.2
  subst middle
  obtain ⟨middleUpper, middleReady, middleValue, middlePrefix⟩ := child actual roots _ _ typed expressionReplay rfl wholeEffect ready
  obtain ⟨next, returned, returnedState, coercedRun, whole, generated, candidate, retained⟩ :=
    middleReady.returnValue loop rfl (fun live => ⟨(middleValue live).bound, (middleValue live).refined⟩)
      sourceContext contextOk checked.1 originBound (by
        have stack := (advB_lowerExpr expression le ls _ _ rfl).stack
        simpa only [stack] using scopes)
  refine ⟨next, returned, returnedState, coercedRun, whole, generated, candidate, ?_⟩
  intro index bound
  have growth : upper.vals.size ≤ middleUpper.vals.size := by
    rw [ready.roots.valueSize, middleReady.roots.valueSize]
    exact (advB_lowerExpr expression le ls _ _ rfl).vals
  exact (retained index (Nat.lt_of_lt_of_le bound growth)).trans (middlePrefix index bound)

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
