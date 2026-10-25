import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlGraphExtensions
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlFrames
import Goose.Lower.Validation.SummaryPreservationReplayBlock
import Goose.Lower.Validation.SummaryPreservationReturnTransfer

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
  {env : PEnv} {root siteRoot : DemandNode} {siteTargets : List BlockId}

theorem blockOccurrenceAction (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId))
    (want : Bool) (scope : ScopeId) (statements : List Stmt) (value : Option Expr)
    (sourceRoots : List RootRef) (type : VTy) (expected : List RootRef)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (sites : OccurrenceSitesBuilder env siteRoot siteTargets le ls func vt upper)
    (targetBounds : ReplacementTargetsBound siteTargets ls)
    (scopeBound : scope < scopeCount)
    (metadata : ∀ binding ∈ bindings,
      binding.1 < le.slots.size ∧ binding.2.2 < le.mod.origins.size)
    (values : ls.cur.isSome = true → ∀ binding ∈ bindings, binding.2.1 < ls.vals.size)
    (roots : ∀ binding ∈ bindings, ∀ root ∈ rootsAt upper.vals binding.2.1,
      root ∈ rootsAt upper.slots binding.1)
    (projects : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func
      (lowerBlock loop bindings want (.mk scope statements value) le ls).2)
    (continuation : NativeBuilderContinuation func (lowerBlock loop bindings want (.mk scope statements value) le ls).2)
    (statementChild : ∀ state provenance,
      state = (initSlots bindings le (Goose.Lower.pushScope scope le
        (Goose.Lower.emitEffect (.enter scope) le ls).2).2).2 →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      OccurrenceSitesBuilder env siteRoot siteTargets le state func vt provenance →
      ReplacementTargetsBound siteTargets state →
      SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func (lowerStmts loop statements le state).2 →
      NativeBuilderContinuation func (lowerStmts loop statements le state).2 →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerStmts loop statements le state).2 next ∧
        (∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) ∧
        ReturnBoundsPreserved expected state provenance (lowerStmts loop statements le state).2 next ∧
        OccurrenceLedger env root func vt next state (lowerStmts loop statements le state).2 ∧
        OccurrenceSitesBuilder env siteRoot siteTargets le (lowerStmts loop statements le state).2 func vt next)
    (valueChild : ∀ state provenance,
      state = (lowerStmts loop statements le (initSlots bindings le
        (Goose.Lower.pushScope scope le (Goose.Lower.emitEffect (.enter scope) le ls).2).2).2).2 →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      OccurrenceSitesBuilder env siteRoot siteTargets le state func vt provenance →
      ReplacementTargetsBound siteTargets state →
      SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func (lowerBlockValue want value le state).2 →
      NativeBuilderContinuation func (lowerBlockValue want value le state).2 →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerBlockValue want value le state).2 next ∧
        (want = true → (lowerBlockValue want value le state).2.cur.isSome = true →
          ReplayValue func next (lowerBlockValue want value le state).2
            (lowerBlockValue want value le state).1 sourceRoots type) ∧
        (∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) ∧
        ReturnBoundsPreserved expected state provenance (lowerBlockValue want value le state).2 next ∧
        OccurrenceLedger env root func vt next state (lowerBlockValue want value le state).2 ∧
        OccurrenceSitesBuilder env siteRoot siteTargets le (lowerBlockValue want value le state).2 func vt next) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerBlock loop bindings want (.mk scope statements value) le ls).2 next ∧
      (want = true → (lowerBlock loop bindings want (.mk scope statements value) le ls).2.cur.isSome = true →
        ReplayValue func next (lowerBlock loop bindings want (.mk scope statements value) le ls).2
          (lowerBlock loop bindings want (.mk scope statements value) le ls).1 sourceRoots type) ∧
      (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
      ReturnBoundsPreserved expected ls upper
        (lowerBlock loop bindings want (.mk scope statements value) le ls).2 next ∧
      OccurrenceLedger env root func vt next ls
        (lowerBlock loop bindings want (.mk scope statements value) le ls).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets le
        (lowerBlock loop bindings want (.mk scope statements value) le ls).2 func vt next := by
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
  have scopedSites : OccurrenceSitesBuilder env siteRoot siteTargets le scopedState func vt upper :=
    (sites.emitEffect (effect := .enter scope) trivial rfl).of_blocks rfl rfl
  have initializedSites := occurrenceSites_initSlots bindings scopedSites
  have pushedExtension : entered.Ext scopedState :=
    (EmitsOnly.of_blocks (property := fun _ => True) rfl).extension
  have initializedExtension : ls.Ext initialized :=
    (advB_emitEffect (.enter scope) le ls _ _ rfl).ext.trans
      (pushedExtension.trans (advB_initSlots bindings le scopedState _ _ rfl).ext)
  have initializedBounds := targetBounds.mono initializedExtension
  let body := lowerStmts loop statements le initialized
  let produced := lowerBlockValue want value le body.2
  have whole : lowerBlock loop bindings want (.mk scope statements value) le ls =
      (produced.1, (Goose.Lower.popScope le (Goose.Lower.emitEffect (.leave scope) le produced.2).2).2) := by
    simp only [lowerBlock, inScope, bind_run, pure_run]
    rfl
  have valueProjects := projects.restrict (by
    intro recipe member
    rw [whole, recipesUnchangedB_popScope, recipesUnchangedB_emitEffect]
    exact member)
  have statementProjects := valueProjects.of_advance
    (advB_lowerBlockValue want value le body.2 _ _ rfl)
  have finalContinuation := continuation
  rw [whole] at finalContinuation
  have valueContinuation := finalContinuation.of_extension
    ((advB_emitEffect (.leave scope) le produced.2 _ _ rfl).ext.trans
      (graphExtension_sameBlocks (by rw [popScope_run]; rfl)))
  have statementContinuation := valueContinuation.of_advance
    (advB_lowerBlockValue want value le body.2 _ _ rfl)
  obtain ⟨middle, bodyReady, bodyRoots, bodyTransfer, bodyLedger, bodySites⟩ :=
    statementChild initialized upper rfl initializedReady initializedSites initializedBounds statementProjects statementContinuation
  obtain ⟨next, valueReady, returned, nextRoots, valueTransfer, valueLedger, valueSites⟩ :=
    valueChild body.2 middle rfl bodyReady bodySites
      (initializedBounds.mono (advB_lowerStmts loop statements le initialized _ _ rfl).ext) valueProjects valueContinuation
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
  refine ⟨next, completed, ?_, ?_, ?_, ?_, ?_⟩
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
  · have nextGrowth : middle.vals.size ≤ next.vals.size := by
      rw [bodyReady.roots.valueSize, valueReady.roots.valueSize]
      exact (advB_lowerBlockValue want value le body.2 _ _ rfl).vals
    have enteredLedger : OccurrenceLedger env root func vt next ls entered :=
      emitsOnly_emitEffect (.enter scope) (InstructionOccurrences.enter scope) le ls _ _ rfl
    have pushedLedger : OccurrenceLedger env root func vt next entered scopedState := .of_blocks rfl
    have prefixLedger : OccurrenceLedger env root func vt next ls initialized :=
      (enteredLedger.trans pushedLedger).trans (occurrenceLedger_initSlots bindings le scopedState _ _ rfl)
    have tailLedger : OccurrenceLedger env root func vt next produced.2
        (Goose.Lower.popScope le (Goose.Lower.emitEffect (.leave scope) le produced.2).2).2 :=
      (emitsOnly_emitEffect _ (InstructionOccurrences.leave _) le produced.2 _ _ rfl).trans (.of_blocks rfl)
    exact ((prefixLedger.trans (bodyLedger.retained nextGrowth nextRoots)).trans valueLedger).trans tailLedger
  · exact (valueSites.emitEffect (effect := .leave scope) trivial rfl).of_blocks rfl rfl

#print axioms blockOccurrenceAction

end Goose.Lower.Validation.ReplacementContentFlowSource
