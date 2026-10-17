import Goose.Lower.Validation.PermissionInstructionControlRangeSteps

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem loopBody_counted_newPermissionInstructions
    {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat} {before after : LS}
    {result : Unit} {condition counter header : ValueId} {hint : IntTy}
    {body : Nat → BlockId → B ValueId}
    (generated : GeneratedBuilderState before) (lower : first ≤ before.vals.size)
    (headerAt : ∃ block, before.blocks[header]? = some block ∧ block.params = [(counter,.data (.int hint))])
    (bodyDense : ∀ depth exit, DenseRun (body depth exit))
    (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (bodyTypes : ∀ depth exit, TypeRun (body depth exit))
    (bodyFrames : ∀ depth exit, GeneratedTargetFrameRun
      (some ⟨depth,exit,.next header hint counter⟩) (body depth exit))
    (bodyNew : ∀ depth exit input value output,
      GeneratedBuilderState input → input.cur.isSome = true → LoopBuilderFrames (some ⟨depth,exit,.next header hint counter⟩) input →
      first ≤ input.vals.size → before.Ext input → before.vals.size ≤ input.vals.size → TypePrefix before input →
      TermEdgesFramed none before input → body depth exit le input = (value,output) →
      NewPermissionInstructions module func le first input output)
    (run : loopBody condition body (rangeBack hint counter header) le before = (result,after)) :
    NewPermissionInstructions module func le first before after ∧
      ∀ instruction, FreshPermissionInstruction module func le first before instruction →
        FreshPermissionInstruction module func le first after instruction := by
  unfold loopBody at run
  simp only [bind_eq] at run
  obtain ⟨saved,initial,savedRun,⟨bodyId,exit⟩,forked,forkRun,ignored,selected,selectedRun,
    value,ended,bodyRun,ignored',closed,backRun,entry⟩ := run
  rw [get_apply] at savedRun
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj savedRun
  have forkGenerated := generated.fork condition forkRun
  have ids := fork_ids forkRun
  have bodyBound : bodyId < forked.blocks.size := by
    have same := congrArg Prod.fst ids.1
    dsimp only at same
    rw [same,ids.2]
    exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
  have selectedGenerated := forkGenerated.setCur (some bodyId)
    (by intro block same; cases same; exact bodyBound) selectedRun
  obtain ⟨head,headRow,headParams⟩ := headerAt
  obtain ⟨forkHead,forkHeadRow,forkHeadParams,_⟩ :=
    (advB_fork condition le before (bodyId,exit) forked forkRun).ext.2 header head headRow
  obtain ⟨exitBlock,exitRow,exitParams⟩ := (fork_emptyRows forkRun).2
  have selectedFrames : LoopBuilderFrames (some ⟨before.stack.length,exit,.next header hint counter⟩) selected := by
    apply loopBuilderFrames_next (exitBlock := exitBlock) (headerBlock := forkHead)
    · rw [setCur_blocks selectedRun]; exact exitRow
    · exact exitParams
    · rw [setCur_blocks selectedRun]; exact forkHeadRow
    · exact forkHeadParams.trans headParams
  have selectedGrowth : before.vals.size ≤ selected.vals.size := by
    have grows := (advB_fork condition le before (bodyId,exit) forked forkRun).vals
    rw [setCur_run] at selectedRun
    obtain ⟨_,rfl⟩ := Prod.mk.inj selectedRun
    exact grows
  have selectedLower := Nat.le_trans lower selectedGrowth
  have forkAdvance := (advB_fork condition le before (bodyId,exit) forked forkRun).ext
  have forkFramed := generatedTargetFrame_fork none condition before le before (bodyId,exit) forked
    (.refl _) trivial (.refl _ _) forkRun
  have selectedFramed := generatedTargetFrame_setCur none (some bodyId) before le forked ignored selected
    forkAdvance trivial forkFramed.1 selectedRun
  have selectedTypes := (types_fork condition le before (bodyId,exit) forked forkRun).trans
    (types_setCur (some bodyId) le forked ignored selected selectedRun)
  have selectedLive : selected.cur.isSome = true := by
    have same := selectedRun
    rw [setCur_run] at same
    obtain ⟨_,rfl⟩ := Prod.mk.inj same
    rfl
  have child := bodyNew before.stack.length exit selected value ended selectedGenerated selectedLive selectedFrames selectedLower
    (forkAdvance.trans selectedFramed.2) selectedGrowth selectedTypes selectedFramed.1 bodyRun
  have endedDense := bodyDense before.stack.length exit le selected value ended bodyRun
    selectedGenerated.dense selectedGenerated.live
  have endedFrames := selectedFrames.mono (bodyAdvance before.stack.length exit le selected value ended bodyRun).ext
  have retainBody : ∀ instruction, FreshPermissionInstruction module func le first ended instruction →
      FreshPermissionInstruction module func le first after instruction := by
    intro instruction permitted
    exact (permitted.rangeBack endedDense.1 endedDense.2.1 endedFrames backRun).setCur entry
  have retainFork : ∀ instruction, FreshPermissionInstruction module func le first forked instruction →
      FreshPermissionInstruction module func le first after instruction := by
    intro instruction permitted
    exact retainBody instruction ((permitted.setCur selectedRun).of_framed_run bodyRun
      (bodyDense _ _) (bodyAdvance _ _) (bodyTypes _ _) (bodyFrames _ _) selectedGenerated selectedFrames)
  constructor
  · have tail : NewPermissionInstructions module func le first selected after := by
      have back : NewPermissionInstructions module func le first ended after :=
        (rangeBack_newPermissionInstructions backRun).append_setCur entry
      intro instruction member
      rcases back instruction member with old | issued
      · exact (child instruction old).imp id (retainBody instruction)
      · exact Or.inr issued
    intro instruction member
    rcases tail instruction member with old | issued
    · have forkMember : instruction ∈ forked.insts := by
        rw [setCur_run] at selectedRun
        obtain ⟨_,rfl⟩ := Prod.mk.inj selectedRun
        exact old
      exact (NewPermissionInstructions.fork forkRun instruction forkMember).imp id (retainFork instruction)
    · exact Or.inr issued
  · intro instruction permitted
    exact retainFork instruction (permitted.of_framed_run forkRun (dense_fork condition)
      (advB_fork condition) (types_fork condition) (generatedTargetFrame_fork none condition) generated trivial)

theorem lowerRange_counted_newPermissionInstructions
    {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat} {before after : LS}
    {result : Unit} {counter bound header : ValueId} {hint : IntTy} {body : Nat → BlockId → B ValueId}
    (generated : GeneratedBuilderState before) (lower : first ≤ before.vals.size)
    (headerAt : ∃ block, before.blocks[header]? = some block ∧ block.params = [(counter,.data (.int hint))])
    (bodyDense : ∀ depth exit, DenseRun (body depth exit))
    (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (bodyTypes : ∀ depth exit, TypeRun (body depth exit))
    (bodyFrames : ∀ depth exit, GeneratedTargetFrameRun
      (some ⟨depth,exit,.next header hint counter⟩) (body depth exit))
    (bodyNew : ∀ depth exit input value output,
      GeneratedBuilderState input → input.cur.isSome = true → LoopBuilderFrames (some ⟨depth,exit,.next header hint counter⟩) input →
      first ≤ input.vals.size → before.Ext input → before.vals.size ≤ input.vals.size → TypePrefix before input →
      TermEdgesFramed none before input → body depth exit le input = (value,output) →
      NewPermissionInstructions module func le first input output)
    (run : lowerRange hint counter bound header body le before = (result,after)) :
    NewPermissionInstructions module func le first before after ∧
      ∀ instruction, FreshPermissionInstruction module func le first before instruction →
        FreshPermissionInstruction module func le first after instruction := by
  unfold lowerRange at run
  obtain ⟨condition,middle,comparison,tail⟩ := bind_eq.mp run
  have middleGenerated := generated.emitDef _ comparison
  have middleLower := Nat.le_trans lower (advB_emitDef _ le before condition middle comparison).vals
  obtain ⟨head,headRow,headParams⟩ := headerAt
  obtain ⟨middleHead,middleRow,middleParams,_⟩ :=
    (advB_emitDef _ le before condition middle comparison).ext.2 header head headRow
  have loop := loopBody_counted_newPermissionInstructions middleGenerated middleLower
    ⟨middleHead,middleRow,middleParams.trans headParams⟩ bodyDense bodyAdvance bodyTypes bodyFrames
    (by
      intro depth exit input value output inputGenerated inputLive inputFrames inputLower prefixExt prefixGrowth prefixTypes prefixFramed run
      have compareExt := (advB_emitDef _ le before condition middle comparison).ext
      have compareFramed := generatedTargetFrame_emitDef none (.cmp .lt hint counter bound)
        before le before condition middle (.refl _) trivial (.refl _ _) comparison
      exact bodyNew depth exit input value output inputGenerated inputLive inputFrames inputLower
        (compareExt.trans prefixExt)
        (Nat.le_trans (advB_emitDef _ le before condition middle comparison).vals prefixGrowth)
        ((types_emitDef _ le before condition middle comparison).trans prefixTypes)
        (compareFramed.1.compose prefixFramed compareExt) run) tail
  constructor
  · exact (NewPermissionInstructions.counting comparison trivial).compose loop.1
      (fun instruction _ permitted => loop.2 instruction permitted)
  · intro instruction permitted
    exact loop.2 instruction (permitted.of_framed_run comparison (dense_emitDef _)
      (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _) generated trivial)

theorem lowerRange_newPermissionInstructions
    {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat} {before after : LS}
    {result : Unit} {counter bound header : ValueId} {hint : IntTy} {body : Nat → BlockId → B ValueId}
    (generated : GeneratedBuilderState before) (lower : first ≤ before.vals.size)
    (headerAt : ∃ block, before.blocks[header]? = some block ∧ block.params = [(counter,.data (.int hint))])
    (bodyDense : ∀ depth exit, DenseRun (body depth exit))
    (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (bodyTypes : ∀ depth exit, TypeRun (body depth exit))
    (bodyFrames : ∀ depth exit, GeneratedTargetFrameRun
      (some ⟨depth,exit,.next header hint counter⟩) (body depth exit))
    (bodyNew : ∀ depth exit input value output,
      GeneratedBuilderState input → input.cur.isSome = true → LoopBuilderFrames (some ⟨depth,exit,.next header hint counter⟩) input →
      first ≤ input.vals.size → before.Ext input → before.vals.size ≤ input.vals.size → TypePrefix before input →
      TermEdgesFramed none before input → body depth exit le input = (value,output) →
      NewPermissionInstructions module func le first input output)
    (run : lowerRange hint counter bound header body le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  exact (lowerRange_counted_newPermissionInstructions generated lower headerAt bodyDense bodyAdvance
    bodyTypes bodyFrames bodyNew run).1

#print axioms loopBody_counted_newPermissionInstructions
#print axioms lowerRange_newPermissionInstructions

end Goose.Lower.Validation
