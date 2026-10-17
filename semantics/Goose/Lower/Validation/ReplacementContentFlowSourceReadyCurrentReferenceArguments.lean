import Goose.Lower.Validation.ReplacementContentFlowSourceReadyRecordedArguments
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyArgumentTypes
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyReferenceArguments
import Goose.Lower.Validation.SourceReadablePlaceShape

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.current_refSlice_argument_content
    {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before after : LS}
    {typingEnv : TEnv} {results : List Ty} {callee : Core.Impl} {parameter : Param}
    {parameters : List Param} {argument : Arg} {arguments : List Arg} {parameterVar : LocalVar}
    {startOffset finishOffset : Nat} {value : ValueId} {provenance : Prov}
    {nativeResults : Array (List RootRef)} {sourceEnv : PEnv} {sourcePlace : Place} {physicalRoots : List RootRef}
    (frame : SourceReadyFrame module callees func types state completed)
    (canonical : state.CanonicalWithin func types provenance)
    (valuesSize : provenance.vals.size = func.numValues)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ result op,
      Inst.def result op ∈ block.insts → result < func.numValues)
    (quiet : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      func.provStep nativeResults types (provenance, false) instruction = (provenance, false))
    (growth : (start func types).Extends state)
    (readable : SourceReadableEnvironment typingEnv)
    (typed : Core.tyArgs typingEnv callee (parameter :: parameters) (argument :: arguments)
      startOffset = .ok ((), finishOffset))
    (mode : parameter.mode = .byRef)
    (parameterRow : callee.vars[parameter.var]? = some parameterVar)
    (reference : parameterVar.ty.isRefSlice = true)
    (generated : GeneratedBuilderState before)
    (run : lowerArg argument (lowerEnv typingEnv.mod typingEnv.vars results) before = (value, after))
    (native : SummaryPreservation.NativeRows types after)
    (live : after.cur.isSome = true)
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (slots : VisibleSlotsReady typingEnv state)
    (seeds : ∀ variableId localVar, typingEnv.vars[variableId]? = some localVar →
      localVar.ty.isRefSlice = true → RootRef.param variableId ∈ rootsAt provenance.slots variableId)
    (physical : ReadAddressPhysical sourceEnv sourcePlace physicalRoots)
    (below : rootsAt provenance.vals value ⊆ physicalRoots)
    (available : flowAt state.values value ≠ .pending) :
    content func state (flowAt state.values value) ≠ .pending := by
  obtain ⟨mu, place, info, childFinish, argumentEq, source, refLike, copyable, writable⟩ :=
    tyArgs_refSlice_head mode parameterRow reference typed
  subst argument
  have cached := source_reference_argument_cached source writable generated run live
  have nativeType := native value _ cached
  have valueBound : value < state.values.size := by
    rw [frame.shape.values, ← frame.values]
    exact Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp cached).1 allocated
  have beforeLive := (dead_lowerArg (.byRef mu place)).live_before run live
  rcases source_readable_place_shape readable source copyable refLike with
    ⟨variableId, localVar, rfl, variableIdRow, infoType⟩ |
    ⟨variableId, localVar, holderMu, sliceMu, element, rfl, variableIdRow, localType, infoType, flat⟩
  · exact frame.current_variable_argument_content canonical valuesSize definitions quiet growth run generated.live
      beforeLive extension physical source refLike slots valueBound nativeType below available
  · let env := lowerEnv typingEnv.mod typingEnv.vars results
    change lowerArg (.byRef mu (.deref (.read (.var variableId)))) env before = (value, after) at run
    let address := Lower.emitDef (.slotAddr variableId) env before
    let loaded := Lower.emitDef (.load address.1) env address.2
    let recorded := (recordReadValueRootRecipe loaded.1 (.var variableId) env loaded.2).2
    have innerRun : lowerExpr (.read (.var variableId)) env before = (loaded.1, recorded) := by
      simp only [lowerExpr_read_run, lowerPlace, address, loaded, recorded]
    have borrowRun : Lower.borrowTo mu loaded.1 env recorded = (value, after) := by
      simpa only [lowerArg, lowerPlace, bind_run, innerRun] using run
    have innerNative : SummaryPreservation.NativeRows types recorded :=
      native.of_prefix (types_borrowTo mu loaded.1 env recorded value after borrowRun)
    have innerLive := (dead_borrowTo mu loaded.1).live_before borrowRun live
    have readNative : SummaryPreservation.NativeRows types
        (lowerExpr (.read (.var variableId)) env before).2 := by
      simpa only [innerRun] using innerNative
    have holderType := readNative.local_read variableIdRow (by
      change (lowerExpr (.read (.var variableId)) env before).2.cur.isSome = true
      rw [innerRun]
      exact innerLive)
    change types[(lowerExpr (.read (.var variableId)) env before).1]? = some (some (.data localVar.ty)) at holderType
    rw [innerRun, localType] at holderType
    have holderReference : valRefLike types loaded.1 = true := by
      simp [valRefLike, holderType, VTy.refLike, Ty.isRefLike]
    have recordRun : recordReadValueRootRecipe loaded.1 (.var variableId) env loaded.2 =
        ((), recorded) := Prod.ext (Subsingleton.elim _ _) rfl
    have seed := seeds variableId localVar variableIdRow (by simp [localType, Ty.isRefSlice, flat])
    exact frame.current_forwarded_argument_content_recorded canonical valuesSize definitions quiet growth
      (show Lower.emitDef (.slotAddr variableId) env before = address from rfl)
      (show Lower.emitDef (.load address.1) env address.2 = loaded from rfl)
      recordRun borrowRun generated.live beforeLive extension seed holderReference physical
      refLike valueBound nativeType below available

#print axioms SourceReadyFrame.current_refSlice_argument_content

end Goose.Lower.Validation.ReplacementContentFlowSource
