import Goose.Lower.Validation.SummaryPreservationReplayControlTransfers

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedBlockStatement {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
    {env output : TEnv} {penv : PEnv} {body : Core.Block} {origin : OriginId}
    {scope start finish : Nat} {before after : RState} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : tyStmt env scope (.expr (.blockE body) origin) start = .ok (output, finish))
    (replayed : rpStmt penv (.expr (.blockE body) origin) before = .ok ((), after))
    (wholeEffect : EffectRefinement func after.eff target)
    (child : ∀ type roots range value state,
      tyBlock (exprEnv env) [] body start = .ok (type, finish) →
      rpBlockValue penv [] body before = .ok ((roots, range), after) →
      lowerBlock none [] true body le ls = (value, state) →
      EffectRefinement func after.eff target →
      ReplayBuilder module results vt func target le scopeCount slots ls upper →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots state next ∧
        ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerStmt loop (.expr (.blockE body) origin) le ls).2 next ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  apply ready.typedExpressionStatement loop source replayed wholeEffect
  intro type roots value state typed expressionReplay run effect stateReady
  obtain ⟨⟨blockRoots, range⟩, middle, blockReplay, returned⟩ := (st_bind_ok _ _ _ _).mp expressionReplay
  have same := (st_pure_ok _ _ _).mp returned
  obtain ⟨rfl, stateEq⟩ := Prod.mk.inj same
  subst middle
  exact child type roots range value state typed blockReplay run effect stateReady

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
