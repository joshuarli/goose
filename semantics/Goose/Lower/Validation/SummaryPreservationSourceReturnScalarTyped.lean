import Goose.Lower.Validation.SummaryPreservationSourceReturnScalarReplay
import Goose.Lower.Validation.SummaryPreservationSourceReturnScalarLedger

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedScalarReturn {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
    {env output : TEnv} {penv : PEnv} {impl : Impl} {expression : Expr} {origin : OriginId}
    {scope start finish : Nat} {before after : RState} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : tyStmt env scope (.ret (some expression) origin) start = .ok (output, finish))
    (replayed : rpStmt penv (.ret (some expression) origin) before = .ok ((), after))
    (implementation : env.impl = some impl)
    (nonref : (impl.results[0]?).any Ty.isRefLike = false)
    (resultTypes : le.results = impl.results.toList)
    (wholeEffect : EffectRefinement func after.eff target)
    (originBound : origin < le.mod.origins.size)
    (scopes : ∀ scope ∈ ls.stack, scope < scopeCount)
    (child : ∀ actual roots value state,
      tyExpr env expression start = .ok (actual, finish) →
      rpExpr penv expression before = .ok (roots, after) →
      lowerExpr expression le ls = (value, state) →
      EffectRefinement func after.eff target →
      ReplayBuilder module results vt func target le scopeCount slots ls upper →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots state next ∧
        (state.cur.isSome = true → ReplayValue func next state value roots (.data actual)) ∧
        ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) :
    ∃ next returned returnedState,
      Goose.Lower.coerceResult (lowerExpr expression le ls).1 origin le (lowerExpr expression le ls).2 =
        (returned, returnedState) ∧
      lowerStmt loop (.ret (some expression) origin) le ls =
        Goose.Lower.emitTerm (.ret [returned] (some origin)) le (Goose.Lower.leaveTo 0 le returnedState).2 ∧
      ReplayBuilder module results vt func target le scopeCount slots
        (lowerStmt loop (.ret (some expression) origin) le ls).2 next ∧
      (returnedState.cur.isSome = true → rootsAt next.vals returned = []) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨expected, actual, resultList, expectedNonref, _, typed, passable⟩ :=
    source_return_scalar_children source implementation nonref
  obtain ⟨roots, middle, expressionReplay, checking⟩ := (st_bind_ok _ _ _ _).mp replayed
  have checked := (liftV_ok _ _ _).mp checking
  have same : after = middle := checked.2
  subst middle
  obtain ⟨next, expressionReady, expressionValue, retained⟩ :=
    child actual roots _ _ typed expressionReplay rfl wholeEffect ready
  have resultHead : le.results.head? = some expected := by rw [resultTypes, resultList]; rfl
  obtain ⟨generated, coercedRun, whole, scalar⟩ := expressionReady.returnScalarValue loop rfl resultHead
    passable expectedNonref expressionValue originBound (by
      have stack := (advB_lowerExpr expression le ls _ _ rfl).stack
      simpa only [stack] using scopes)
  exact ⟨next, (lowerExpr expression le ls).1, (lowerExpr expression le ls).2,
    coercedRun, whole, generated, scalar, retained⟩

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
