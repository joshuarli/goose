import Goose.Lower.Validation.SummaryPreservationReplayInitialSlots
import Goose.Lower.Validation.SummaryPreservationReplayValue
import Goose.Lower.Validation.SummaryPreservationReplayLiveEmit

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem blockValue (want : Bool) (value : Option Expr) (sourceRoots : List RootRef) (type : VTy)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (missing : value = none → sourceRoots = [] ∧ type = .data .unit)
    (child : ∀ expression, value = some expression →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerExpr expression le ls).2 next ∧
        ((lowerExpr expression le ls).2.cur.isSome = true →
          ReplayValue func next (lowerExpr expression le ls).2
            (lowerExpr expression le ls).1 sourceRoots type) ∧
        ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerBlockValue want value le ls).2 next ∧
      (want = true → (lowerBlockValue want value le ls).2.cur.isSome = true →
        ReplayValue func next (lowerBlockValue want value le ls).2
          (lowerBlockValue want value le ls).1 sourceRoots type) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases value with
  | some expression =>
    obtain ⟨next, generated, returned, retained⟩ := child expression rfl
    exact ⟨next, generated, fun _ => returned, retained⟩
  | none =>
    obtain ⟨rfl, rfl⟩ := missing rfl
    cases want with
    | false => exact ⟨upper, ready, by simp, fun _ _ => rfl⟩
    | true =>
      obtain ⟨next, generated, returned, retained⟩ := ready.emitTypedDef .constUnit [] (.data .unit)
        (by simp [Op.uses]) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
        (effectRefinement_empty func target) (fun _ member => by cases member) (fun _ => rfl)
      exact ⟨next, generated, fun _ => returned, retained⟩

theorem blockAction (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId))
    (want : Bool) (scope : ScopeId) (statements : List Stmt) (value : Option Expr)
    (sourceRoots : List RootRef) (type : VTy)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (scopeBound : scope < scopeCount)
    (metadata : ∀ binding ∈ bindings,
      binding.1 < le.slots.size ∧ binding.2.2 < le.mod.origins.size)
    (values : ls.cur.isSome = true → ∀ binding ∈ bindings, binding.2.1 < ls.vals.size)
    (roots : ∀ binding ∈ bindings, ∀ root ∈ rootsAt upper.vals binding.2.1,
      root ∈ rootsAt upper.slots binding.1)
    (statementChild : ∀ state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerStmts loop statements le state).2 next ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    (valueChild : ∀ state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerBlockValue want value le state).2 next ∧
        (want = true → (lowerBlockValue want value le state).2.cur.isSome = true →
          ReplayValue func next (lowerBlockValue want value le state).2
            (lowerBlockValue want value le state).1 sourceRoots type) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerBlock loop bindings want (.mk scope statements value) le ls).2 next ∧
      (want = true → (lowerBlock loop bindings want (.mk scope statements value) le ls).2.cur.isSome = true →
        ReplayValue func next (lowerBlock loop bindings want (.mk scope statements value) le ls).2
          (lowerBlock loop bindings want (.mk scope statements value) le ls).1 sourceRoots type) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  let entered := (Goose.Lower.emitEffect (.enter scope) le ls).2
  let scopedState := (Goose.Lower.pushScope scope le entered).2
  let initialized := (initSlots bindings le scopedState).2
  have enteredReady := ready.enter scope scopeBound
  have scopedReady := enteredReady.pushScope scope
  have sameValues : scopedState.vals = ls.vals := by
    cases current : ls.cur with
    | none => simp [scopedState, entered, emitEffect_none _ _ current, pushScope_run, current]
    | some block => simp [scopedState, entered, emitEffect_run _ _ current, pushScope_run, current]
  have sameCurrent : scopedState.cur = ls.cur := by
    cases current : ls.cur with
    | none => simp [scopedState, entered, emitEffect_none _ _ current, pushScope_run, current]
    | some block => simp [scopedState, entered, emitEffect_run _ _ current, pushScope_run, current]
  have scopedValues : scopedState.cur.isSome = true → ∀ binding ∈ bindings,
      binding.2.1 < scopedState.vals.size := by
    rw [sameCurrent, sameValues]
    exact values
  have initializedReady := scopedReady.initialSlots bindings metadata scopedValues roots
  obtain ⟨middle, bodyReady, bodyRoots⟩ := statementChild initialized upper initializedReady
  let body := lowerStmts loop statements le initialized
  obtain ⟨next, valueReady, returned, nextRoots⟩ := valueChild body.2 middle bodyReady
  let produced := lowerBlockValue want value le body.2
  have leaveReady := valueReady.leave scope scopeBound
  have completed := leaveReady.popScope
  have leavingValues : (Goose.Lower.emitEffect (.leave scope) le produced.2).2.vals = produced.2.vals := by
    cases current : produced.2.cur with
    | none => rw [emitEffect_none _ _ current]
    | some block => rw [emitEffect_run _ _ current]
  have leavingCurrent : (Goose.Lower.emitEffect (.leave scope) le produced.2).2.cur = produced.2.cur := by
    cases current : produced.2.cur with
    | none => rw [emitEffect_none _ _ current]; exact current
    | some block => rw [emitEffect_run _ _ current]; exact current
  have whole : lowerBlock loop bindings want (.mk scope statements value) le ls =
      (produced.1, (Goose.Lower.popScope le (Goose.Lower.emitEffect (.leave scope) le produced.2).2).2) := by
    simp only [lowerBlock, inScope, bind_run, pure_run]
    rfl
  rw [whole]
  refine ⟨next, completed, ?_, ?_⟩
  · intro wanted live
    have producedLive : produced.2.cur.isSome = true := by
      simpa only [popScope_run, leavingCurrent] using live
    have result := returned wanted producedLive
    refine ⟨?_, result.refined, result.scalar⟩
    simpa only [popScope_run, leavingValues] using result.bound
  · intro index bound
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [initializedReady.roots.valueSize, bodyReady.roots.valueSize]
      exact (advB_lowerStmts loop statements le initialized body.1 body.2 rfl).vals
    exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (bodyRoots index bound)

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
