import Goose.Lower.Validation.ReplacementContentFlowSourceReadyContentReads
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyRecording

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

private theorem content_read_visible {env : TEnv} {variableId : VarId} {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.read (.deref (.read (.var variableId)))) start = .ok (type, finish)) :
    variableId ∈ env.visible := by
  by_cases visible : variableId ∈ env.visible
  · exact visible
  · obtain ⟨info, offset, placeSource, _⟩ := tyExpr_read_place source
    simp [Core.tyPlace, Core.sliceRefTy, Core.tyExpr, Core.varOf, visible, chk, rej_ok] at placeSource

private theorem definition_current {operation : Op} {env : LEnv} {before after : LS} {value : ValueId}
    (run : Lower.emitDef operation env before = (value, after)) : after.cur = before.cur := by
  cases current : before.cur with
  | none =>
    rw [emitDef_none _ _ current] at run
    simpa only [Function.comp_apply, current] using congrArg (LS.cur ∘ Prod.snd) run.symm
  | some block =>
    rw [emitDef_run _ _ current] at run
    simpa only [Function.comp_apply, current] using congrArg (LS.cur ∘ Prod.snd) run.symm

theorem SourceReadyFrame.sourceContentRead {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before first middle after : LS}
    {typingEnv : TEnv} {results : List Ty} {variableId : VarId} {localVar : LocalVar}
    {slotAddress holder value : ValueId} {mutability sliceMutability : Mutability} {element type : Ty}
    {typingStart typingFinish : Nat} {provenance : Prov}
    (frame : SourceReadyFrame module callees func types state completed)
    (canonical : state.CanonicalWithin func types provenance)
    (growth : (start func types).Extends state)
    (source : Core.tyExpr typingEnv (.read (.deref (.read (.var variableId)))) typingStart = .ok (type, typingFinish))
    (variableRow : typingEnv.vars[variableId]? = some localVar)
    (localType : localVar.ty = .ref mutability (.slice sliceMutability element))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types after)
    (slots : VisibleSlotsReady typingEnv state)
    (placeRun : lowerPlace (.var variableId) (lowerEnv typingEnv.mod typingEnv.vars results) before = (slotAddress, first))
    (innerRun : Lower.emitDef (.load slotAddress) (lowerEnv typingEnv.mod typingEnv.vars results) first = (holder, middle))
    (outerRun : Lower.emitDef (.load holder) (lowerEnv typingEnv.mod typingEnv.vars results) middle = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (slotRoots : before.cur.isSome = true → rootsAt provenance.vals slotAddress ⊆ [.local variableId])
    (holderRoots : before.cur.isSome = true → rootsAt provenance.vals holder ⊆ [.param variableId]) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  have visible := content_read_visible source
  have checkedPlace : Core.tyPlace typingEnv (.var variableId) typingStart =
      .ok ({ ty := localVar.ty, bindingWritable := localVar.kind == .mutable, contentsWritable := true }, typingStart) := by
    simp [Core.tyPlace, Core.varOf, visible, variableRow, chk, pure, StateT.pure, bind, StateT.bind, Except.pure, Except.bind]
  cases current : before.cur with
  | none =>
    have deadPlace := placeRun
    change Lower.emitDef (.slotAddr variableId) env before = (slotAddress, first) at deadPlace
    rw [emitDef_none _ _ current] at deadPlace
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj deadPlace
    rw [emitDef_none _ _ current] at innerRun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj innerRun
    rw [emitDef_none _ _ current] at outerRun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj outerRun
    exact ⟨.refl _ _, by simp [current]⟩
  | some block =>
    have active : before.cur.isSome = true := by simp [current]
    have firstCurrent := (definition_current placeRun).trans current
    have middleCurrent := (definition_current innerRun).trans firstCurrent
    have firstLive : first.cur.isSome = true := by simp [firstCurrent]
    have middleLive : middle.cur.isSome = true := by simp [middleCurrent]
    have middleNative := native.of_prefix (types_emitDef (.load holder) env middle value after outerRun)
    have firstNative := middleNative.of_prefix (types_emitDef (.load slotAddress) env first holder middle innerRun)
    obtain ⟨slotMutability, slotTag⟩ := firstNative.place generated checkedPlace placeRun firstLive
    let recorded := (recordReadValueRootRecipe holder (.var variableId) env middle).2
    have unchanged := readRecording_preserves holder (.var variableId) env middle
    have innerSource : lowerExpr (.read (.var variableId)) (lowerEnv typingEnv.mod typingEnv.vars results) before = (holder, recorded) := by
      simp only [lowerExpr_read_run, env, placeRun, innerRun, recorded]
    have innerNative : SummaryPreservation.NativeRows types
        (lowerExpr (.read (.var variableId)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
      rw [innerSource]
      intro id tag row
      exact middleNative id tag (by simpa only [recorded, unchanged.2.1] using row)
    have innerTag := innerNative.local_read variableRow (by simpa only [innerSource, recorded, unchanged.2.2] using middleLive)
    simp only [innerSource] at innerTag
    have holderTag := innerTag
    rw [localType] at holderTag
    have slotExact := placeRun
    change Lower.emitDef (.slotAddr variableId) env before = (slotAddress, first) at slotExact
    rw [emitDef_run _ _ current] at slotExact
    have slotId : slotAddress = before.vals.size := (Prod.mk.inj slotExact).1.symm
    have firstSize : first.vals.size = before.vals.size + 1 := by
      simpa only [Array.size_push] using congrArg (fun pair => pair.2.vals.size) slotExact.symm
    have innerExact := innerRun
    rw [emitDef_run _ _ firstCurrent] at innerExact
    have holderId : holder = first.vals.size := (Prod.mk.inj innerExact).1.symm
    have middleSize : middle.vals.size = first.vals.size + 1 := by
      simpa only [Array.size_push] using congrArg (fun pair => pair.2.vals.size) innerExact.symm
    have outerExact := outerRun
    rw [emitDef_run _ _ middleCurrent] at outerExact
    have afterSize : after.vals.size = middle.vals.size + 1 := by
      simpa only [Array.size_push] using congrArg (fun pair => pair.2.vals.size) outerExact.symm
    have holderBound : holder < state.values.size := by
      rw [frame.shape.values, ← frame.values, holderId]
      apply Nat.lt_of_lt_of_le _ allocated
      rw [afterSize, middleSize]
      exact Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)
    have slotBound : slotAddress < state.values.size := by
      apply Nat.lt_trans _ holderBound
      rw [slotId, holderId, firstSize]
      exact Nat.lt_succ_self _
    exact frame.contentRead canonical growth placeRun innerRun outerRun extension allocated generated.live
      visible variableRow slots slotBound holderBound slotTag innerTag holderTag (slotRoots active) (holderRoots active)

#print axioms SourceReadyFrame.sourceContentRead

#print axioms content_read_visible

end Goose.Lower.Validation.ReplacementContentFlowSource
