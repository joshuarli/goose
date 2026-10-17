import Goose.Lower.Validation.ReplacementContentFlowSourceReadyContentSource
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyReadBounds
import Goose.Lower.Validation.FreshRunSource

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

private theorem definition_current {operation : Op} {env : LEnv} {before after : LS} {value : ValueId}
    (run : Lower.emitDef operation env before = (value, after)) : after.cur = before.cur := by
  cases current : before.cur with
  | none =>
    rw [emitDef_none _ _ current] at run
    simpa only [Function.comp_apply, current] using congrArg (LS.cur ∘ Prod.snd) run.symm
  | some block =>
    rw [emitDef_run _ _ current] at run
    simpa only [Function.comp_apply, current] using congrArg (LS.cur ∘ Prod.snd) run.symm

theorem SourceReadyFrame.content_address_bounds {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before first middle after : LS}
    {env : LEnv} {variableId : VarId} {slotAddress holder value : ValueId}
    {provenance ghost : Prov} {sourceEnv : PEnv} {root : DemandNode} {resultRoots : Array (List RootRef)}
    (frame : SourceReadyFrame module callees func types state completed)
    (valuesSize : provenance.vals.size = func.numValues)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → value < func.numValues)
    (quiet : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      func.provStep resultRoots types (provenance, false) instruction = (provenance, false))
    (origins : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      InstructionOccurrences sourceEnv root func types ghost instruction)
    (below : ∀ index, rootsAt provenance.vals index ⊆ rootsAt ghost.vals index)
    (seed : RootRef.param variableId ∈ rootsAt provenance.slots variableId)
    (generated : GeneratedBuilderState before)
    (slotRun : Lower.emitDef (.slotAddr variableId) env before = (slotAddress, first))
    (innerRun : Lower.emitDef (.load slotAddress) env first = (holder, middle))
    (outerRun : Lower.emitDef (.load holder) env middle = (value, after))
    (extension : after.Ext completed)
    (innerReference : valRefLike types holder = true)
    (outerReference : valRefLike types value = true)
    (live : before.cur.isSome = true) :
    rootsAt provenance.vals slotAddress ⊆ [.local variableId] ∧
      rootsAt provenance.vals holder ⊆ [.param variableId] := by
  cases current : before.cur with
  | none => simp [current] at live
  | some block =>
    have firstCurrent : first.cur = some block := (definition_current slotRun).trans current
    have middleCurrent : middle.cur = some block := (definition_current innerRun).trans firstCurrent
    have firstGenerated := generated.emitDef (.slotAddr variableId) slotRun
    have middleGenerated := firstGenerated.emitDef (.load slotAddress) innerRun
    obtain ⟨addressBlock, addressMember, addressInstruction⟩ := emitted_definition_retained current
      (generated.live block current) slotRun
      ((adv_emitDef innerRun).ext.trans ((adv_emitDef outerRun).ext.trans extension)) frame.blocks
    obtain ⟨holderBlock, holderBlockMember, holderInstruction⟩ := emitted_definition_retained firstCurrent
      (firstGenerated.live block firstCurrent) innerRun ((adv_emitDef outerRun).ext.trans extension) frame.blocks
    obtain ⟨valueBlock, valueMember, valueInstruction⟩ := emitted_definition_retained middleCurrent
      (middleGenerated.live block middleCurrent) outerRun extension frame.blocks
    have innerOccurrence := (origins holderBlock holderBlockMember _ holderInstruction).2.1 holder slotAddress rfl innerReference
    have slotBound : slotAddress < provenance.vals.size := by
      rw [valuesSize]
      exact definitions addressBlock addressMember _ _ addressInstruction
    have slotMember : RootRef.local variableId ∈ rootsAt provenance.vals slotAddress :=
      provStep_def_roots slotBound (quiet addressBlock addressMember _ addressInstruction) (by simp [rootsOfDef])
    have holderBound : holder < provenance.vals.size := by
      rw [valuesSize]
      exact definitions holderBlock holderBlockMember _ _ holderInstruction
    have holderMember := load_local_parameter_seed holderBound (quiet holderBlock holderBlockMember _ holderInstruction)
      innerReference slotMember seed
    have outerOccurrence := (origins valueBlock valueMember _ valueInstruction).2.1 value holder rfl outerReference
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, physical⟩ := outerOccurrence
    exact ⟨innerOccurrence.slot_address_upper (below slotAddress) slotBound
      (quiet addressBlock addressMember _ addressInstruction), physical.parameter_upper (below holder) holderMember⟩

theorem SourceReadyFrame.sourceContentRead_of_occurrences {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before first middle after : LS}
    {typingEnv : TEnv} {results : List Ty} {variableId : VarId} {localVar : LocalVar}
    {slotAddress holder value : ValueId} {mutability sliceMutability : Mutability} {element type : Ty}
    {typingStart typingFinish : Nat} {provenance ghost : Prov} {sourceEnv : PEnv} {root : DemandNode}
    {resultRoots : Array (List RootRef)}
    (frame : SourceReadyFrame module callees func types state completed)
    (canonical : state.CanonicalWithin func types provenance)
    (valuesSize : provenance.vals.size = func.numValues)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → value < func.numValues)
    (quiet : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      func.provStep resultRoots types (provenance, false) instruction = (provenance, false))
    (growth : (start func types).Extends state)
    (origins : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      InstructionOccurrences sourceEnv root func types ghost instruction)
    (below : ∀ index, rootsAt provenance.vals index ⊆ rootsAt ghost.vals index)
    (seed : RootRef.param variableId ∈ rootsAt provenance.slots variableId)
    (source : Core.tyExpr typingEnv (.read (.deref (.read (.var variableId)))) typingStart = .ok (type, typingFinish))
    (reference : type.isRefLike = true)
    (variableRow : typingEnv.vars[variableId]? = some localVar)
    (localType : localVar.ty = .ref mutability (.slice sliceMutability element))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types after)
    (slots : VisibleSlotsReady typingEnv state)
    (placeRun : lowerPlace (.var variableId) (lowerEnv typingEnv.mod typingEnv.vars results) before = (slotAddress, first))
    (innerRun : Lower.emitDef (.load slotAddress) (lowerEnv typingEnv.mod typingEnv.vars results) first = (holder, middle))
    (outerRun : Lower.emitDef (.load holder) (lowerEnv typingEnv.mod typingEnv.vars results) middle = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  have bounds : before.cur.isSome = true →
      rootsAt provenance.vals slotAddress ⊆ [.local variableId] ∧
      rootsAt provenance.vals holder ⊆ [.param variableId] := by
    intro live
    let env := lowerEnv typingEnv.mod typingEnv.vars results
    have firstCurrent := definition_current placeRun
    have middleCurrent := definition_current innerRun
    have afterCurrent := definition_current outerRun
    have middleLive : middle.cur.isSome = true := by rw [middleCurrent, firstCurrent]; exact live
    have afterLive : after.cur.isSome = true := by rw [afterCurrent]; exact middleLive
    have middleNative := native.of_prefix (types_emitDef (.load holder) env middle value after outerRun)
    let recorded := (recordReadValueRootRecipe holder (.var variableId) env middle).2
    have unchanged := readRecording_preserves holder (.var variableId) env middle
    have innerSource : lowerExpr (.read (.var variableId)) env before = (holder, recorded) := by
      simp only [lowerExpr_read_run, env, placeRun, innerRun, recorded]
    have innerNative : SummaryPreservation.NativeRows types
        (lowerExpr (.read (.var variableId)) env before).2 := by
      rw [innerSource]
      intro id tag row
      exact middleNative id tag (by simpa only [recorded, unchanged.2.1] using row)
    have innerTag := innerNative.local_read variableRow
      (show (lowerExpr (.read (.var variableId)) env before).2.cur.isSome = true from by
        rw [innerSource]
        exact unchanged.2.2 ▸ middleLive)
    rw [innerSource, localType] at innerTag
    have innerReference : valRefLike types holder = true := by simp [valRefLike, innerTag, VTy.refLike, Ty.isRefLike]
    let evaluated := Lower.emitDef (.load holder) env recorded
    have tailSame := readRecording_definition holder (.var variableId) (.load holder) env middle
    change evaluated.1 = (Lower.emitDef (.load holder) env middle).1 ∧
      evaluated.2.blocks = (Lower.emitDef (.load holder) env middle).2.blocks ∧
      evaluated.2.vals = (Lower.emitDef (.load holder) env middle).2.vals ∧
      evaluated.2.cur = (Lower.emitDef (.load holder) env middle).2.cur at tailSame
    rw [outerRun] at tailSame
    have run : lowerExpr (.read (.deref (.read (.var variableId)))) env before = evaluated := by
      rw [typedRead_run source results before]
      change (do
        let address ← lowerExpr (.read (.var variableId))
        Lower.emitDef (.load address)) env before = evaluated
      simp only [bind_run, innerSource, evaluated]
    have evaluatedNative : SummaryPreservation.NativeRows types evaluated.2 := by
      intro id tag row
      exact native id tag (tailSame.2.2.1 ▸ row)
    have evaluatedLive : evaluated.2.cur.isSome = true := by
      rw [tailSame.2.2.2]
      exact afterLive
    have tag : types[evaluated.1]? = some (some (.data type)) :=
      evaluatedNative.expression generated source run evaluatedLive
    rw [tailSame.1] at tag
    have outerReference : valRefLike types value = true := by simp [valRefLike, tag, VTy.refLike, reference]
    exact frame.content_address_bounds valuesSize definitions quiet origins below seed generated placeRun innerRun outerRun
      extension innerReference outerReference live
  exact frame.sourceContentRead canonical growth source variableRow localType generated native slots
    placeRun innerRun outerRun extension allocated (fun live => (bounds live).1) (fun live => (bounds live).2)

#print axioms SourceReadyFrame.sourceContentRead_of_occurrences

#print axioms SourceReadyFrame.content_address_bounds

end Goose.Lower.Validation.ReplacementContentFlowSource
