import Goose.Lower.Validation.SummaryPreservationReplayBlock
import Goose.Lower.Validation.SummaryPreservationReturnTransfer

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem blockActionTracked (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId))
    (want : Bool) (scope : ScopeId) (statements : List Stmt) (value : Option Expr)
    (sourceRoots : List RootRef) (type : VTy) (expected : List RootRef)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (scopeBound : scope < scopeCount)
    (metadata : ∀ binding ∈ bindings,
      binding.1 < le.slots.size ∧ binding.2.2 < le.mod.origins.size)
    (values : ls.cur.isSome = true → ∀ binding ∈ bindings, binding.2.1 < ls.vals.size)
    (roots : ∀ binding ∈ bindings, ∀ root ∈ rootsAt upper.vals binding.2.1,
      root ∈ rootsAt upper.slots binding.1)
    (statementChild : ∀ state provenance,
      state = (initSlots bindings le (Goose.Lower.pushScope scope le
        (Goose.Lower.emitEffect (.enter scope) le ls).2).2).2 →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerStmts loop statements le state).2 next ∧
        (∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) ∧
        ReturnBoundsPreserved expected state provenance (lowerStmts loop statements le state).2 next)
    (valueChild : ∀ state provenance,
      state = (lowerStmts loop statements le (initSlots bindings le
        (Goose.Lower.pushScope scope le (Goose.Lower.emitEffect (.enter scope) le ls).2).2).2).2 →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerBlockValue want value le state).2 next ∧
        (want = true → (lowerBlockValue want value le state).2.cur.isSome = true →
          ReplayValue func next (lowerBlockValue want value le state).2
            (lowerBlockValue want value le state).1 sourceRoots type) ∧
        (∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) ∧
        ReturnBoundsPreserved expected state provenance (lowerBlockValue want value le state).2 next) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerBlock loop bindings want (.mk scope statements value) le ls).2 next ∧
      (want = true → (lowerBlock loop bindings want (.mk scope statements value) le ls).2.cur.isSome = true →
        ReplayValue func next (lowerBlock loop bindings want (.mk scope statements value) le ls).2
          (lowerBlock loop bindings want (.mk scope statements value) le ls).1 sourceRoots type) ∧
      (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
      ReturnBoundsPreserved expected ls upper
        (lowerBlock loop bindings want (.mk scope statements value) le ls).2 next := by
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
  obtain ⟨middle, bodyReady, bodyRoots, bodyTransfer⟩ := statementChild initialized upper rfl initializedReady
  let body := lowerStmts loop statements le initialized
  obtain ⟨next, valueReady, returned, nextRoots, valueTransfer⟩ := valueChild body.2 middle rfl bodyReady
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
  have enteredFrame := ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_emitEffect (.enter scope))
    le ls () entered rfl
  have pushedFrame : ReturnMembershipFrame entered scopedState := by
    change ReturnMembershipFrame entered (Goose.Lower.pushScope scope le entered).2
    rw [pushScope_run]
    exact fun _ _ member => member
  have initializedFrame := ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_initSlots bindings)
    le scopedState () initialized rfl
  have prefixTransfer : ReturnBoundsPreserved expected ls upper initialized upper :=
    ReturnBoundsPreserved.frame ready.symbols ready.roots.valueSize (fun _ _ => rfl)
      (enteredFrame.trans (pushedFrame.trans initializedFrame))
  have leftFrame := ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_emitEffect (.leave scope))
    le produced.2 () (Goose.Lower.emitEffect (.leave scope) le produced.2).2 rfl
  have poppedFrame : ReturnMembershipFrame (Goose.Lower.emitEffect (.leave scope) le produced.2).2
      (Goose.Lower.popScope le (Goose.Lower.emitEffect (.leave scope) le produced.2).2).2 := by
    rw [popScope_run]
    exact fun _ _ member => member
  have tailTransfer := ReturnBoundsPreserved.frame (expected := expected) valueReady.symbols
    valueReady.roots.valueSize (fun _ _ => rfl) (leftFrame.trans poppedFrame)
  rw [whole]
  refine ⟨next, completed, ?_, ?_, ?_⟩
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

  · exact ((prefixTransfer.trans bodyTransfer).trans valueTransfer).trans tailTransfer

#print axioms blockActionTracked

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
