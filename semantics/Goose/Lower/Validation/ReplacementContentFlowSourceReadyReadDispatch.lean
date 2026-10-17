import Goose.Lower.Validation.ReplacementContentFlowSourceReadyContentOrigins
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyReadSource
import Goose.Lower.Validation.SourceReadablePlaceShape

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.sourceRead {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS}
    {typingEnv : TEnv} {results : List Ty} {place : Place} {type : Ty}
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
    (seeds : ∀ variableId localVar, typingEnv.vars[variableId]? = some localVar →
      localVar.ty.isRefSlice = true → RootRef.param variableId ∈ rootsAt provenance.slots variableId)
    (readable : SourceReadableEnvironment typingEnv)
    (source : Core.tyExpr typingEnv (.read place) typingStart = .ok (type, typingFinish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerExpr (.read place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (slots : VisibleSlotsReady typingEnv state)
    (extension : (lowerExpr (.read place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerExpr (.read place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (child : ∀ info finish, Core.tyPlace typingEnv place typingStart = .ok (info, finish) →
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before) :
    ValueReadyAt state (lowerExpr (.read place)) (lowerEnv typingEnv.mod typingEnv.vars results) before := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  change SummaryPreservation.NativeRows types (lowerExpr (.read place) env before).2 at native
  change (lowerExpr (.read place) env before).2.Ext completed at extension
  change (lowerExpr (.read place) env before).2.vals.size ≤ completed.vals.size at allocated
  by_cases reference : type.isRefLike = true
  · rcases source_read_expression_shape readable source reference with
      ⟨variableId, localVar, rfl, variableRow, rfl⟩ |
      ⟨variableId, localVar, mu, sliceMu, element, rfl, variableRow, localType, rfl, elementFlat⟩
    · let address := lowerPlace (.var variableId) env before
      let output := Lower.emitDef (.load address.1) env address.2
      have actual : lowerExpr (.read (.var variableId)) env before = output := by
        exact typedRead_run source results before
      have result := frame.sourceLocalRead_of_occurrences canonical valuesSize definitions quiet growth origins below
        source reference generated (by change SummaryPreservation.NativeRows types output.2; rw [← actual]; exact native) slots
        (show lowerPlace (.var variableId) env before = address from rfl)
        (show Lower.emitDef (.load address.1) env address.2 = output from rfl)
        (by change output.2.Ext completed; rw [← actual]; exact extension) (by change output.2.vals.size ≤ completed.vals.size; rw [← actual]; exact allocated)
      change EmitsOnly (ReadyOperands state) before (lowerExpr _ env before).2 ∧ _
      rw [actual]
      exact result
    · let address := lowerPlace (.var variableId) env before
      let holder := Lower.emitDef (.load address.1) env address.2
      let output := Lower.emitDef (.load holder.1) env holder.2
      let recorded := (recordReadValueRootRecipe holder.1 (.var variableId) env holder.2).2
      let evaluated := Lower.emitDef (.load holder.1) env recorded
      have inner : lowerExpr (.read (.var variableId)) env before = (holder.1, recorded) := by
        simp only [lowerExpr_read_run, address, holder, recorded]
      have actual : lowerExpr (.read (.deref (.read (.var variableId)))) env before = evaluated := by
        rw [typedRead_run source results before]
        change (do
          let address ← lowerExpr (.read (.var variableId))
          Lower.emitDef (.load address)) env before = evaluated
        simp only [bind_run, inner, evaluated]
      have unchanged := readRecording_definition holder.1 (.var variableId) (.load holder.1) env holder.2
      change evaluated.1 = output.1 ∧ evaluated.2.blocks = output.2.blocks ∧
        evaluated.2.vals = output.2.vals ∧ evaluated.2.cur = output.2.cur at unchanged
      have outputNative : SummaryPreservation.NativeRows types output.2 := by
        intro id tag row
        apply native id tag
        rw [actual, unchanged.2.2.1]
        exact row
      have outputExtension : output.2.Ext completed := by
        have current : evaluated.2.Ext completed := by simpa only [actual] using extension
        simpa only [LS.Ext, unchanged.2.1] using current
      have outputAllocated : output.2.vals.size ≤ completed.vals.size := by
        simpa only [actual, unchanged.2.2.1] using allocated
      have seed := seeds variableId localVar variableRow (by simp [localType, Ty.isRefSlice, elementFlat])
      have result := frame.sourceContentRead_of_occurrences canonical valuesSize definitions quiet growth origins below seed
        source reference variableRow localType generated outputNative slots
        (show lowerPlace (.var variableId) env before = address from rfl)
        (show Lower.emitDef (.load address.1) env address.2 = holder from rfl)
        (show Lower.emitDef (.load holder.1) env holder.2 = output from rfl)
        outputExtension outputAllocated
      change EmitsOnly (ReadyOperands state) before (lowerExpr _ env before).2 ∧ _
      rw [actual]
      refine ⟨result.1.trans (.of_blocks unchanged.2.1), ?_⟩
      intro live
      rw [unchanged.1]
      exact result.2 (by simpa only [unchanged.2.2.2] using live)
  · have scalar : type.isRefLike = false := Bool.eq_false_iff.mpr reference
    obtain ⟨info, finish, placeSource, _⟩ := tyExpr_read_place source
    let address := lowerPlace place env before
    have result := frame.sourceScalarRead source scalar generated native (show lowerPlace place env before = address from rfl)
      (show lowerExpr (.read place) env before = lowerExpr (.read place) env before from rfl)
      extension allocated (child info finish placeSource)
    exact result

#print axioms SourceReadyFrame.sourceRead

end Goose.Lower.Validation.ReplacementContentFlowSource
