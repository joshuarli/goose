import Goose.Lower.Validation.PermissionInstructionControlEachSteps
import Goose.Lower.Validation.PermissionInstructionControlRange

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lowerEach_counted_newPermissionInstructions
    {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat} {before after : LS}
    {result : Unit} {counter header sampled : ValueId} {regrow : Bool} {owner : Option ValueId}
    {body : Nat → BlockId → B ValueId}
    (generated : GeneratedBuilderState before) (lower : first ≤ before.vals.size)
    (headerAt : ∃ block, before.blocks[header]? = some block ∧ block.params = [(counter,.data (.int .i64))])
    (counterRecorded : before.vals[counter]? = some (some (.data (.int .i64))))
    (bodyDense : ∀ depth exit, DenseRun (body depth exit))
    (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (bodyTypes : ∀ depth exit, TypeRun (body depth exit))
    (bodyFrames : ∀ depth exit, GeneratedTargetFrameRun
      (some ⟨depth,exit,.next header .i64 counter⟩) (body depth exit))
    (bodyNew : ∀ depth exit input value output,
      GeneratedBuilderState input → input.cur.isSome = true → LoopBuilderFrames (some ⟨depth,exit,.next header .i64 counter⟩) input →
      input.vals[counter]? = some (some (.data (.int .i64))) →
      first ≤ input.vals.size → before.Ext input → before.vals.size ≤ input.vals.size →
      TypePrefix before input → TermEdgesFramed none before input →
      body depth exit le input = (value,output) → NewPermissionInstructions module func le first input output)
    (run : lowerEach regrow owner sampled header counter body le before = (result,after)) :
    NewPermissionInstructions module func le first before after ∧
      ∀ instruction, FreshPermissionInstruction module func le first before instruction →
        FreshPermissionInstruction module func le first after instruction := by
  unfold lowerEach at run
  simp only [bind_eq] at run
  obtain ⟨length,measured,measureRun,condition,compared,compareRun,loopRun⟩ := run
  have measuredGenerated := generated.eachLen regrow owner sampled measureRun
  have measuredAdvance := advB_eachLen regrow owner sampled le before length measured measureRun
  have comparedGenerated := measuredGenerated.emitDef _ compareRun
  have comparedAdvance := advB_emitDef _ le measured condition compared compareRun
  have beforeCompared := measuredAdvance.ext.trans comparedAdvance.ext
  have valuesCompared := Nat.le_trans measuredAdvance.vals comparedAdvance.vals
  have typesCompared := (types_eachLen regrow owner sampled le before length measured measureRun).trans
    (types_emitDef _ le measured condition compared compareRun)
  have measuredFrames := generatedTargetFrame_eachLen none regrow owner sampled before le before length measured
    (.refl _) trivial (.refl none before) measureRun
  have comparedFrames := generatedTargetFrame_emitDef none (.cmp .lt .i64 counter length)
    before le measured condition compared measuredAdvance.ext trivial measuredFrames.1 compareRun
  obtain ⟨head,headRow,headParams⟩ := headerAt
  obtain ⟨comparedHead,comparedHeadRow,comparedHeadParams,_⟩ := beforeCompared.2 header head headRow
  have loop := loopBody_counted_newPermissionInstructions comparedGenerated (Nat.le_trans lower valuesCompared)
    ⟨comparedHead,comparedHeadRow,comparedHeadParams.trans headParams⟩
    bodyDense bodyAdvance bodyTypes bodyFrames
    (fun depth exit input value output gen live frames floor extension grows types terms childRun =>
      bodyNew depth exit input value output gen live frames
        ((typesCompared.trans types) _ _ counterRecorded) floor (beforeCompared.trans extension)
        (Nat.le_trans valuesCompared grows) (typesCompared.trans types)
        (comparedFrames.1.compose terms beforeCompared) childRun) loopRun
  have measuredNew := NewPermissionInstructions.eachLen (module := module) (func := func) (first := first) measureRun
  have comparedNew := measuredNew.compose_framed (NewPermissionInstructions.counting compareRun trivial)
    compareRun (dense_emitDef _) (advB_emitDef _) (types_emitDef _)
    (generatedTargetFrame_emitDef none _) measuredGenerated trivial
  constructor
  · exact comparedNew.compose loop.1 (fun instruction _ permitted => loop.2 instruction permitted)
  · intro instruction permitted
    have atMeasured := permitted.of_framed_run measureRun (dense_eachLen regrow owner sampled)
      (advB_eachLen regrow owner sampled) (types_eachLen regrow owner sampled)
      (generatedTargetFrame_eachLen none regrow owner sampled) generated trivial
    exact loop.2 instruction (atMeasured.of_framed_run compareRun (dense_emitDef _)
      (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _) measuredGenerated trivial)

#print axioms lowerEach_counted_newPermissionInstructions

end Goose.Lower.Validation
