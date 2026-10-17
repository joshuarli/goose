import Goose.Lower.Validation.SummaryPreservationReplayBuilder
import Goose.Lower.Validation.SummaryPreservationStatementReplay

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem statements {env : PEnv} (loop : Option LoopCtx) (body : List Stmt)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (step : ∀ statement before after state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      rpStmt env statement before = .ok ((), after) → state.cur.isSome = true →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerStmt loop statement le state).2 next ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    {before after : RState} (source : rpStmts env body before = .ok ((), after)) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerStmts loop body le ls).2 next ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have localStep : ∀ statement before after state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      rpStmt env statement before = .ok ((), after) → state.cur.isSome = true →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerStmt loop statement le state).2 next ∧ next.slots = provenance.slots ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index := by
    intro statement before after state provenance stateReady replayed live
    obtain ⟨next, nextReady, growth⟩ := step statement before after state provenance stateReady replayed live
    exact ⟨next, nextReady, nextReady.slotsEq.trans stateReady.slotsEq.symm, growth⟩
  obtain ⟨next, nextReady, _, growth⟩ := lowerStmts_source_composition
    (fun state provenance => ReplayBuilder module results vt func target le scopeCount slots state provenance)
    loop localStep body (fun _ _ stateReady => stateReady.roots.valueSize) ready source
  exact ⟨next, nextReady, growth⟩

theorem inScope_value (scope : ScopeId) (action : B ValueId) (sourceRoots : List RootRef)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (step : ∀ state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots (action le state).2 next ∧
        ((action le state).2.cur.isSome = true →
          RootsRefine func (rootsAt next.vals (action le state).1) sourceRoots) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (inScope scope action le ls).2 next ∧
      ((inScope scope action le ls).2.cur.isSome = true →
        RootsRefine func (rootsAt next.vals (inScope scope action le ls).1) sourceRoots) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨next, nextReady, roots, growth⟩ := step _ _ (ready.pushScope scope)
  have finished := nextReady.popScope
  simp only [inScope, bind_run, pure_run]
  refine ⟨next, finished, ?_, growth⟩
  simpa only [popScope_run] using roots

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
