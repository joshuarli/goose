import Goose.Lower.Validation.ReplacementContentFlowSourceReadyCurrentArguments
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyRecording

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before after : LS}
  {provenance : Prov} {results : Array (List RootRef)} {env : LEnv}
  {output : ValueId} {mutability : Mutability}

theorem SourceReadyFrame.native_forwarded_argument_root_recorded
    (frame : SourceReadyFrame module callees func types state completed)
    (valuesSize : provenance.vals.size = func.numValues)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → value < func.numValues)
    (quiet : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      func.provStep results types (provenance, false) instruction = (provenance, false))
    {variableId : VarId} {address holder : ValueId} {first loaded middle : LS}
    (slotRun : Lower.emitDef (.slotAddr variableId) env before = (address, first))
    (loadRun : Lower.emitDef (.load address) env first = (holder, loaded))
    (recordRun : recordReadValueRootRecipe holder (.var variableId) env loaded = ((), middle))
    (borrowRun : Lower.borrowTo mutability holder env middle = (output, after))
    (bounded : LiveBound before) (live : before.cur.isSome = true)
    (extension : after.Ext completed)
    (seed : RootRef.param variableId ∈ rootsAt provenance.slots variableId)
    (reference : valRefLike types holder = true) :
    RootRef.param variableId ∈ rootsAt provenance.vals output := by
  have borrowAdvance := advB_borrowTo mutability holder env middle output after borrowRun
  have recordAdvance := advB_recordReadValueRootRecipe holder (.var variableId) env loaded () middle recordRun
  have loadedExtension := recordAdvance.ext.trans (borrowAdvance.ext.trans extension)
  have loadAdvance := adv_emitDef loadRun
  have firstExtension := loadAdvance.ext.trans loadedExtension
  have slotMember := frame.native_definition_root valuesSize definitions quiet slotRun bounded live firstExtension
    (show RootRef.local variableId ∈ rootsOfDef results types func provenance address (.slotAddr variableId) from by simp [rootsOfDef])
  have firstBound := liveBound_of_adv (adv_emitDef slotRun) bounded
  have firstLive : first.cur.isSome = true := by
    cases current : before.cur with
    | none => simp [current] at live
    | some block =>
      have actual := slotRun
      rw [emitDef_run _ _ current] at actual
      simpa only [current, Option.isSome_some] using congrArg (fun pair => pair.2.cur.isSome) actual.symm
  have loadedLive : loaded.cur.isSome = true := by
    cases current : first.cur with
    | none => simp [current] at firstLive
    | some block =>
      have actual := loadRun
      rw [emitDef_run _ _ current] at actual
      simpa only [current, Option.isSome_some] using congrArg (fun pair => pair.2.cur.isSome) actual.symm
  have holderMember : RootRef.param variableId ∈ rootsAt provenance.vals holder := by
    apply frame.native_definition_root valuesSize definitions quiet loadRun firstBound firstLive loadedExtension
    simp only [rootsOfDef, reference, ite_true]
    apply (unionRoots_mem_iff _ _ _).mpr
    exact Or.inl (List.mem_flatMap.mpr ⟨.local variableId, slotMember, seed⟩)
  have unchanged := readRecording_preserves holder (.var variableId) env loaded
  rw [recordRun] at unchanged
  change middle.blocks = loaded.blocks ∧ middle.vals = loaded.vals ∧ middle.cur = loaded.cur at unchanged
  have middleLive : middle.cur.isSome = true := by simpa only [unchanged.2.2] using loadedLive
  exact frame.native_borrowTo_root valuesSize definitions quiet borrowRun
    (liveBound_of_adv recordAdvance (liveBound_of_adv loadAdvance firstBound)) middleLive extension holderMember

theorem SourceReadyFrame.current_forwarded_argument_content_recorded
    (frame : SourceReadyFrame module callees func types state completed)
    (canonical : state.CanonicalWithin func types provenance)
    (valuesSize : provenance.vals.size = func.numValues)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → value < func.numValues)
    (quiet : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      func.provStep results types (provenance, false) instruction = (provenance, false))
    (growth : (start func types).Extends state)
    {variableId : VarId} {address holder : ValueId} {first loaded middle : LS} {payload : Ty}
    {sourceEnv : PEnv} {sourcePlace : Place} {physicalRoots : List RootRef} {nativeMutability : Mutability}
    (slotRun : Lower.emitDef (.slotAddr variableId) env before = (address, first))
    (loadRun : Lower.emitDef (.load address) env first = (holder, loaded))
    (recordRun : recordReadValueRootRecipe holder (.var variableId) env loaded = ((), middle))
    (borrowRun : Lower.borrowTo mutability holder env middle = (output, after))
    (bounded : LiveBound before) (live : before.cur.isSome = true)
    (extension : after.Ext completed)
    (seed : RootRef.param variableId ∈ rootsAt provenance.slots variableId)
    (holderReference : valRefLike types holder = true)
    (physical : ReadAddressPhysical sourceEnv sourcePlace physicalRoots)
    (reference : payload.isRefLike = true)
    (valueBound : output < state.values.size)
    (native : types[output]? = some (some (.data (.ref nativeMutability payload))))
    (below : rootsAt provenance.vals output ⊆ physicalRoots)
    (available : flowAt state.values output ≠ .pending) :
    content func state (flowAt state.values output) ≠ .pending := by
  have member := frame.native_forwarded_argument_root_recorded valuesSize definitions quiet slotRun loadRun
    recordRun borrowRun bounded live extension seed holderReference
  exact physical.parameter_content_ready canonical growth reference valueBound native below member available

#print axioms SourceReadyFrame.native_forwarded_argument_root_recorded
#print axioms SourceReadyFrame.current_forwarded_argument_content_recorded

end Goose.Lower.Validation.ReplacementContentFlowSource
