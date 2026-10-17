import Goose.Lower.Validation.ReplacementContentFlowSourceReadyLocalReads
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyReadBounds
import Goose.Lower.Validation.FreshRunSource
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyRecording

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

private theorem emitted_current {operation : Op} {env : LEnv} {before after : LS} {value : ValueId}
    (run : Lower.emitDef operation env before = (value, after)) : after.cur = before.cur := by
  cases current : before.cur with
  | none =>
    rw [emitDef_none _ _ current] at run
    simpa only [Function.comp_apply, current] using congrArg (LS.cur ∘ Prod.snd) run.symm
  | some block =>
    rw [emitDef_run _ _ current] at run
    simpa only [Function.comp_apply, current] using congrArg (LS.cur ∘ Prod.snd) run.symm

theorem SourceReadyFrame.sourceScalarRead {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before first after : LS}
    {typingEnv : TEnv} {results : List Ty} {place : Place} {address value : ValueId} {type : Ty}
    {start finish : Nat}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyExpr typingEnv (.read place) start = .ok (type, finish))
    (scalar : type.isRefLike = false)
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types after)
    (placeRun : lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before = (address, first))
    (run : lowerExpr (.read place) (lowerEnv typingEnv.mod typingEnv.vars results) before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (child : EmitsOnly (ReadyOperands state) before first ∧
      (first.cur.isSome = true → flowAt state.values address ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  have loadRun : Lower.emitDef (.load address) (lowerEnv typingEnv.mod typingEnv.vars results) first = (value, after) := by
    simpa only [typedRead_run source, placeRun] using run
  exact frame.scalarRead placeRun loadRun extension allocated (generated.lowerPlace place placeRun).live child
    (fun live => native.expression generated source run (by simpa only [emitted_current loadRun] using live)) scalar

theorem SourceReadyFrame.sourceLocalRead {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before first after : LS}
    {typingEnv : TEnv} {results : List Ty} {variableId : VarId} {address value : ValueId} {type : Ty}
    {start finish : Nat} {provenance : Prov}
    (frame : SourceReadyFrame module callees func types state completed)
    (canonical : state.CanonicalWithin func types provenance)
    (growth : (Goose.GIR.ReplacementContentFlow.Model.start func types).Extends state)
    (source : Core.tyExpr typingEnv (.read (.var variableId)) start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types after)
    (slots : VisibleSlotsReady typingEnv state)
    (placeRun : lowerPlace (.var variableId) (lowerEnv typingEnv.mod typingEnv.vars results) before = (address, first))
    (loadRun : Lower.emitDef (.load address) (lowerEnv typingEnv.mod typingEnv.vars results) first = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (addressRoots : before.cur.isSome = true → rootsAt provenance.vals address ⊆ [.local variableId]) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  have run : lowerExpr (.read (.var variableId)) env before = (value, after) := by
    simpa only [typedRead_run source, env, placeRun] using loadRun
  obtain ⟨info, offset, checkedPlace, typeShape⟩ := tyExpr_read_place source
  have checkedVariable := checkedPlace
  simp only [Core.tyPlace] at checkedVariable
  obtain ⟨localVar, next, checkedLookup, checkedInfo⟩ := (st_bind_ok _ _ _ _).mp checkedVariable
  obtain ⟨visible, variableRow, _⟩ := (varOf_ok _ _ _ _).mp checkedLookup
  have infoType : info.ty = localVar.ty := by
    have equalInfo := congrArg Prod.fst ((st_pure_ok _ _ _).mp checkedInfo)
    exact congrArg PlaceInfo.ty equalInfo
  have resultType : type = localVar.ty := typeShape.trans infoType
  cases current : before.cur with
  | none =>
    have noAddress := placeRun
    change Lower.emitDef (.slotAddr variableId) env before = (address, first) at noAddress
    rw [emitDef_none _ _ current] at noAddress
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj noAddress
    rw [emitDef_none _ _ current] at loadRun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj loadRun
    exact ⟨.refl _ _, by simp [current]⟩
  | some block =>
    have active : before.cur.isSome = true := by simp [current]
    have addressCurrent := emitted_current placeRun
    have firstLive : first.cur.isSome = true := by simpa only [addressCurrent] using active
    have afterLive : after.cur.isSome = true := by simpa only [emitted_current loadRun] using firstLive
    have firstNative := native.of_prefix (types_emitDef (.load address) env first value after loadRun)
    obtain ⟨mutability, addressTag⟩ := firstNative.place generated checkedPlace placeRun firstLive
    rw [infoType] at addressTag
    have valueTag := native.expression generated source run afterLive
    rw [resultType] at valueTag
    have beforeAddress := placeRun
    change Lower.emitDef (.slotAddr variableId) env before = (address, first) at beforeAddress
    rw [emitDef_run _ _ current] at beforeAddress
    have addressId : address = before.vals.size := (Prod.mk.inj beforeAddress).1.symm
    have firstSize : first.vals.size = before.vals.size + 1 := by
      simpa only [Array.size_push] using congrArg (fun pair => pair.2.vals.size) beforeAddress.symm
    have loadExact := loadRun
    cases firstCurrent : first.cur with
    | none => simp [firstCurrent] at firstLive
    | some firstBlock =>
      rw [emitDef_run _ _ firstCurrent] at loadExact
      have afterSize : after.vals.size = first.vals.size + 1 := by
        simpa only [Array.size_push] using congrArg (fun pair => pair.2.vals.size) loadExact.symm
      have addressBound : address < state.values.size := by
        rw [frame.shape.values, ← frame.values, addressId]
        apply Nat.lt_of_lt_of_le _ allocated
        rw [afterSize, firstSize]
        exact Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)
      exact frame.localRead canonical growth placeRun loadRun extension allocated generated.live
        visible variableRow slots addressBound addressTag valueTag (addressRoots active)

theorem SourceReadyFrame.sourceLocalRead_of_occurrences {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before first after : LS}
    {typingEnv : TEnv} {results : List Ty} {variableId : VarId} {address value : ValueId} {type : Ty}
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
    (source : Core.tyExpr typingEnv (.read (.var variableId)) typingStart = .ok (type, typingFinish))
    (reference : type.isRefLike = true)
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types after)
    (slots : VisibleSlotsReady typingEnv state)
    (placeRun : lowerPlace (.var variableId) (lowerEnv typingEnv.mod typingEnv.vars results) before = (address, first))
    (loadRun : Lower.emitDef (.load address) (lowerEnv typingEnv.mod typingEnv.vars results) first = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  apply frame.sourceLocalRead canonical growth source generated native slots placeRun loadRun extension allocated
  intro live
  cases current : before.cur with
  | none => simp [current] at live
  | some block =>
    let env := lowerEnv typingEnv.mod typingEnv.vars results
    have addressRun : Lower.emitDef (.slotAddr variableId) env before = (address, first) := placeRun
    obtain ⟨addressBlock, addressMember, addressInstruction⟩ := emitted_definition_retained current
      (generated.live block current) addressRun ((adv_emitDef loadRun).ext.trans extension) frame.blocks
    have firstCurrent : first.cur = some block := (emitted_current addressRun).trans current
    obtain ⟨valueBlock, valueMember, valueInstruction⟩ := emitted_definition_retained firstCurrent
      ((generated.lowerPlace (.var variableId) placeRun).live block firstCurrent) loadRun extension frame.blocks
    have run : lowerExpr (.read (.var variableId)) env before = (value, after) := by
      simpa only [typedRead_run source, env, placeRun] using loadRun
    have afterLive : after.cur.isSome = true := by
      rw [emitted_current loadRun, firstCurrent]
      rfl
    have tag := native.expression generated source run afterLive
    have referenceValue : valRefLike types value = true := by simp [valRefLike, tag, VTy.refLike, reference]
    have occurrence := (origins valueBlock valueMember _ valueInstruction).2.1 value address rfl referenceValue
    apply occurrence.slot_address_upper (below address)
    · rw [valuesSize]
      exact definitions addressBlock addressMember address (.slotAddr variableId) addressInstruction
    · exact quiet addressBlock addressMember _ addressInstruction

#print axioms SourceReadyFrame.sourceLocalRead_of_occurrences

#print axioms SourceReadyFrame.sourceLocalRead

#print axioms SourceReadyFrame.sourceScalarRead

end Goose.Lower.Validation.ReplacementContentFlowSource
