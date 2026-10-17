import Goose.Lower.Validation.ReplacementContentFlowSourceReadyReadSource
import Goose.Lower.Validation.DereferenceTyping

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.sourceHolderRead {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS}
    {typingEnv : TEnv} {results : List Ty} {variableId : VarId} {localVar : LocalVar}
    {provenance ghost : Prov} {sourceEnv : PEnv} {root : DemandNode} {resultRoots : Array (List RootRef)}
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
    (visible : variableId ∈ typingEnv.visible)
    (variableRow : typingEnv.vars[variableId]? = some localVar)
    (reference : localVar.ty.isRefLike = true)
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.read (.var variableId)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (slots : VisibleSlotsReady typingEnv state)
    (extension : (lowerExpr (.read (.var variableId)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerExpr (.read (.var variableId)) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size) :
    ValueReadyAt state (lowerExpr (.read (.var variableId))) (lowerEnv typingEnv.mod typingEnv.vars results) before := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  change SummaryPreservation.NativeRows types (lowerExpr (.read (.var variableId)) env before).2 at native
  change (lowerExpr (.read (.var variableId)) env before).2.Ext completed at extension
  change (lowerExpr (.read (.var variableId)) env before).2.vals.size ≤ completed.vals.size at allocated
  let address := lowerPlace (.var variableId) env before
  let output := Lower.emitDef (.load address.1) env address.2
  let recorded := (recordReadValueRootRecipe output.1 (.var variableId) env output.2).2
  have unchanged := readRecording_preserves output.1 (.var variableId) env output.2
  have run : lowerExpr (.read (.var variableId)) env before = (output.1, recorded) := by
    simp only [lowerExpr_read_run, address, output, recorded]
  have recordRun : recordReadValueRootRecipe output.1 (.var variableId) env output.2 =
      ((), recorded) := Prod.ext (Subsingleton.elim _ _) rfl
  have outputNative : SummaryPreservation.NativeRows types output.2 := by
    apply native.of_prefix
    rw [run]
    exact types_recordReadValueRootRecipe output.1 (.var variableId) env output.2 () recorded recordRun
  have outputExtension : output.2.Ext completed := by
    have suffix := advB_recordReadValueRootRecipe output.1 (.var variableId) env output.2 () recorded recordRun
    exact suffix.ext.trans (by simpa only [run] using extension)
  have outputAllocated : output.2.vals.size ≤ completed.vals.size := by
    simpa only [run, recorded, unchanged.2.1] using allocated
  have unrecorded : EmitsOnly (ReadyOperands state) before output.2 ∧
      (output.2.cur.isSome = true → flowAt state.values output.1 ≠ .pending) := by
    cases current : before.cur with
    | none =>
      have addressDead : address = (0, before) := by
        exact emitDef_none (.slotAddr variableId) env current
      simp only [output, addressDead, emitDef_none (.load 0) env current]
      exact ⟨.refl _ _, by simp [current]⟩
    | some block =>
      have addressRun : Lower.emitDef (.slotAddr variableId) env before = address := rfl
      have firstCurrent : address.2.cur = some block := by
        have actual := addressRun
        rw [emitDef_run _ _ current] at actual
        simpa only [current] using congrArg (fun pair => pair.2.cur) actual.symm
      have loadRun : Lower.emitDef (.load address.1) env address.2 = output := rfl
      have afterCurrent : output.2.cur = some block := by
        have actual := loadRun
        rw [emitDef_run _ _ firstCurrent] at actual
        simpa only [firstCurrent] using congrArg (fun pair => pair.2.cur) actual.symm
      have afterLive : output.2.cur.isSome = true := by simp [afterCurrent]
      have valueType := native.local_read variableRow (by change (lowerExpr (.read (.var variableId)) env before).2.cur.isSome = true; rw [run]; simpa only [recorded, unchanged.2.2] using afterLive)
      change types[(lowerExpr (.read (.var variableId)) env before).1]? = some (some (.data localVar.ty)) at valueType
      rw [run] at valueType
      have placeSource : Core.tyPlace typingEnv (.var variableId) 0 =
          .ok ({ ty := localVar.ty, bindingWritable := localVar.kind == .mutable, contentsWritable := true }, 0) := by
        simp [Core.tyPlace, Core.varOf, visible, variableRow, chk, pure, StateT.pure, bind, StateT.bind, Except.pure, Except.bind]
      have firstNative := outputNative.of_prefix (types_emitDef (.load address.1) env address.2 output.1 output.2 loadRun)
      obtain ⟨mu, addressType⟩ := firstNative.place generated placeSource rfl (by simp [firstCurrent])
      obtain ⟨addressBlock, addressMember, addressInstruction⟩ := emitted_definition_retained current
        (generated.live block current) addressRun ((adv_emitDef loadRun).ext.trans outputExtension) frame.blocks
      obtain ⟨valueBlock, valueMember, valueInstruction⟩ := emitted_definition_retained firstCurrent
        ((generated.emitDef (.slotAddr variableId) addressRun).live block firstCurrent) loadRun outputExtension frame.blocks
      have innerReference : valRefLike types output.1 = true := by simp [valRefLike, valueType, VTy.refLike, reference]
      have occurrence := (origins valueBlock valueMember _ valueInstruction).2.1 output.1 address.1 rfl innerReference
      have addressBound : address.1 < provenance.vals.size := by
        rw [valuesSize]
        exact definitions addressBlock addressMember _ _ addressInstruction
      have rawUpper := occurrence.slot_address_upper (below address.1) addressBound
        (quiet addressBlock addressMember _ addressInstruction)
      have stateBound : address.1 < state.values.size := by simpa only [canonical.shape.values, valuesSize] using addressBound
      exact frame.localRead canonical growth rfl loadRun outputExtension outputAllocated generated.live
        visible variableRow slots stateBound addressType valueType rawUpper
  change EmitsOnly (ReadyOperands state) before (lowerExpr (.read (.var variableId)) env before).2 ∧ _
  rw [run]
  exact readRecording_ready unrecorded

theorem SourceReadyFrame.sourceSliceReferencePlace {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS}
    {typingEnv : TEnv} {results : List Ty} {variableId : VarId} {target : Ty}
    {provenance ghost : Prov} {sourceEnv : PEnv} {root : DemandNode} {resultRoots : Array (List RootRef)}
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
    (special : Core.sliceRefTy typingEnv (.read (.var variableId)) = some target)
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerPlace (.deref (.read (.var variableId))) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (slots : VisibleSlotsReady typingEnv state)
    (extension : (lowerPlace (.deref (.read (.var variableId))) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerPlace (.deref (.read (.var variableId))) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size) :
    ValueReadyAt state (lowerPlace (.deref (.read (.var variableId)))) (lowerEnv typingEnv.mod typingEnv.vars results) before := by
  obtain ⟨localVar, variableRow, localType, visible⟩ := sliceRefTy_variable_row special
  have refSlice := sliceRefTy_isRefSlice special
  have reference : localVar.ty.isRefLike = true := by
    have targetReference : target.isRefLike = true := by
      cases target <;> simp_all [Ty.isRefLike, Ty.isRefSlice]
    simpa only [localType] using targetReference
  exact frame.sourceHolderRead canonical valuesSize definitions quiet growth origins below
    visible variableRow reference generated native slots extension allocated

#print axioms SourceReadyFrame.sourceSliceReferencePlace

#print axioms SourceReadyFrame.sourceHolderRead

end Goose.Lower.Validation.ReplacementContentFlowSource
