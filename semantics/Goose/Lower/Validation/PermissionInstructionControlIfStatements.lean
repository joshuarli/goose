import Goose.Lower.Validation.PermissionInstructionControlBranches

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem patchBrs0_values {le : LEnv} {target : BlockId} :
    ∀ (pending : List BlockId) {before after : LS} {result : Unit},
      patchBrs0 target pending le before = (result,after) → after.vals = before.vals := by
  intro pending
  induction pending with
  | nil =>
    intro before after result run
    rw [patchBrs0,pure_run] at run
    exact (Prod.mk.inj run).2.symm ▸ rfl
  | cons block rest induction =>
    intro before after result run
    simp only [patchBrs0,bind_eq] at run
    obtain ⟨ignored,middle,patched,finished⟩ := run
    rw [induction finished]
    rw [patchTerm_run] at patched
    obtain ⟨_,rfl⟩ := Prod.mk.inj patched
    rfl

theorem NewPermissionInstructions.patchBrs0 {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {target : BlockId} : ∀ (pending : List BlockId) {before after : LS} {result : Unit},
    Goose.Lower.patchBrs0 target pending le before = (result,after) →
    NewPermissionInstructions module func le first before after := by
  intro pending
  induction pending with
  | nil =>
    intro before after result run
    rw [Goose.Lower.patchBrs0,pure_run] at run
    obtain ⟨_,rfl⟩ := Prod.mk.inj run
    exact .of_blocks_eq rfl
  | cons block rest induction =>
    intro before after result run
    simp only [Goose.Lower.patchBrs0,bind_eq] at run
    obtain ⟨ignored,middle,patched,finished⟩ := run
    intro instruction member
    rcases induction finished instruction member with old | fresh
    · rw [patchTerm_run] at patched
      obtain ⟨_,rfl⟩ := Prod.mk.inj patched
      rcases permission_appendInst_membership (before := before) (block := block)
          (added := .term (.br target [])) old with original | rfl
      · exact Or.inl original
      · exact Or.inr (FreshPermissionInstruction.branch module func le first after target [])
    · exact Or.inr fresh

theorem NewPermissionInstructions.joinArms {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : Unit} {yes no : Option BlockId}
    (run : Goose.Lower.joinArms yes no le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  unfold Goose.Lower.joinArms at run
  split at run
  · exact .setCur run
  · simp only [bind_eq] at run
    obtain ⟨join,allocated,allocation,ignored,patched,patchRun,entry⟩ := run
    exact (NewPermissionInstructions.patchBrs0 _ patchRun).append_setCur entry |>.prepend_newBlock allocation

theorem FreshPermissionInstruction.joinArms {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : Unit} {yes no : Option BlockId} {instruction : Inst}
    (permitted : FreshPermissionInstruction module func le first before instruction)
    (generated : GeneratedBuilderState before)
    (run : Goose.Lower.joinArms yes no le before = (result,after)) :
    FreshPermissionInstruction module func le first after instruction := by
  have framed := generatedTargetFrame_joinArms none yes no before le before result after
    (.refl _) trivial (.refl none before) run
  have afterDense := (dense_joinArms yes no le before result after run generated.dense generated.live).1
  have values : after.vals = before.vals := by
    unfold Goose.Lower.joinArms at run
    split at run
    · rw [setCur_run] at run
      obtain ⟨_,rfl⟩ := Prod.mk.inj run
      rfl
    · simp only [bind_eq] at run
      obtain ⟨join,allocated,allocation,ignored,patched,patchRun,entry⟩ := run
      rw [setCur_run] at entry
      obtain ⟨_,rfl⟩ := Prod.mk.inj entry
      rw [patchBrs0_values _ patchRun]
      rw [newBlock0_run] at allocation
      obtain ⟨_,rfl⟩ := Prod.mk.inj allocation
      rfl
  exact permitted.retained (loop := none) generated.dense afterDense framed.2 (by simp only [values, Nat.le_refl])
    (types_joinArms yes no le before result after run) trivial framed.1

theorem lowerIfSome_newPermissionInstructions {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : Unit} {loop : Option LoopCtx} {origin : OriginId} {condition : Expr} {yes no : Core.Block}
    (generated : GeneratedBuilderState before)
    (frames : LoopBuilderFrames loop before)
    (conditions : ∀ {input output : LS} {value : ValueId}, GeneratedBuilderState input →
      lowerExpr condition le input = (value,output) → NewPermissionInstructions module func le first input output)
    (yesBranch : ∀ {input output : LS} {value : ValueId}, GeneratedBuilderState input → LoopBuilderFrames loop input →
      lowerBlock loop [] false yes le input = (value,output) → NewPermissionInstructions module func le first input output)
    (noBranch : ∀ {input output : LS} {value : ValueId}, GeneratedBuilderState input → LoopBuilderFrames loop input →
      lowerBlock loop [] false no le input = (value,output) → NewPermissionInstructions module func le first input output)
    (run : lowerStmt loop (.ifS condition yes (some no) origin) le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerStmt,bind_eq] at run
  obtain ⟨cv,conditionAfter,conditionRun,run⟩ := run
  have conditionRules := conditions generated conditionRun
  have conditionGenerated := generated.lowerExpr condition conditionRun
  have conditionFrames := frames.mono (advB_lowerExpr condition le before cv conditionAfter conditionRun).ext
  cases live : conditionAfter.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at run
    obtain ⟨_,rfl⟩ := Prod.mk.inj run
    exact conditionRules
  | some current =>
    rw [whenLive_some _ _ _ live] at run
    simp only [bind_eq] at run
    obtain ⟨⟨yesId,noId⟩,forked,forkRun,ignored,yesInput,yesEntry,
      yesValue,yesAfter,yesRun,yesEnd,yesRead,yesReadRun,ignored,noInput,noEntry,
      noValue,noAfter,noRun,noEnd,noRead,noReadRun,joining⟩ := run
    rw [curBlock_run] at yesReadRun noReadRun
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj yesReadRun
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj noReadRun
    have forkedGenerated := conditionGenerated.fork cv forkRun
    have forkedFrames := conditionFrames.mono (advB_fork cv le conditionAfter (yesId,noId) forked forkRun).ext
    have ids := fork_ids forkRun
    have yesBound : yesId < forked.blocks.size := by
      have same := congrArg Prod.fst ids.1
      dsimp only at same
      rw [same,ids.2]
      nat_omega
    have noBound : noId < forked.blocks.size := by
      have same := congrArg Prod.snd ids.1
      dsimp only at same
      rw [same,ids.2]
      nat_omega
    have yesGenerated := forkedGenerated.setCur (some yesId)
      (by intro block same; cases same; exact yesBound) yesEntry
    have yesFrames := forkedFrames.of_blocks (setCur_blocks yesEntry)
    have yesAfterGenerated := yesGenerated.lowerBlock loop [] false yes yesFrames.toTargets yesRun
    have yesAfterFrames := yesFrames.mono (advB_lowerBlock loop [] false yes le yesInput yesValue yesAfter yesRun).ext
    have noTarget : noId < yesAfter.blocks.size := by
      have growth := (advB_lowerBlock loop [] false yes le yesInput yesValue yesAfter yesRun).ext.1
      rw [setCur_blocks yesEntry] at growth
      exact Nat.lt_of_lt_of_le noBound growth
    have noGenerated := yesAfterGenerated.setCur (some noId)
      (by intro block same; cases same; exact noTarget) noEntry
    have noFrames := yesAfterFrames.of_blocks (setCur_blocks noEntry)
    have noAfterGenerated := noGenerated.lowerBlock loop [] false no noFrames.toTargets noRun
    have retainedYes : ∀ instruction, FreshPermissionInstruction module func le first yesAfter instruction →
        FreshPermissionInstruction module func le first after instruction := by
      intro instruction permitted
      have atNo := permitted.setCur noEntry
      have afterNo := atNo.of_framed_run noRun (dense_lowerBlock loop [] false no)
        (advB_lowerBlock loop [] false no) (types_lowerBlock loop [] false no)
        (generatedTargetFrame_lowerBlock loop [] false no) noGenerated noFrames
      exact afterNo.joinArms noAfterGenerated joining
    have retainedFork : ∀ instruction, FreshPermissionInstruction module func le first forked instruction →
        FreshPermissionInstruction module func le first after instruction := by
      intro instruction permitted
      have atYes := permitted.setCur yesEntry
      have afterYes := atYes.of_framed_run yesRun (dense_lowerBlock loop [] false yes)
        (advB_lowerBlock loop [] false yes) (types_lowerBlock loop [] false yes)
        (generatedTargetFrame_lowerBlock loop [] false yes) yesGenerated yesFrames
      exact retainedYes instruction afterYes
    have retainedCondition : ∀ instruction,
        FreshPermissionInstruction module func le first conditionAfter instruction →
        FreshPermissionInstruction module func le first after instruction := by
      intro instruction permitted
      exact retainedFork instruction (permitted.of_framed_run forkRun (dense_fork cv)
        (advB_fork cv) (types_fork cv) (generatedTargetFrame_fork none cv) conditionGenerated trivial)
    have yesRules := (yesBranch yesGenerated yesFrames yesRun).prepend_setCur yesEntry
    have noRules := (noBranch noGenerated noFrames noRun).prepend_setCur noEntry
    intro instruction member
    rcases NewPermissionInstructions.joinArms joining instruction member with old | issued
    · rcases noRules instruction old with old | issued
      · rcases yesRules instruction old with old | issued
        · rcases NewPermissionInstructions.fork forkRun instruction old with old | issued
          · exact (conditionRules instruction old).imp id (retainedCondition instruction)
          · exact Or.inr (retainedFork instruction issued)
        · exact Or.inr (retainedYes instruction issued)
      · exact Or.inr (issued.joinArms noAfterGenerated joining)
    · exact Or.inr issued


theorem lowerIfNone_newPermissionInstructions {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : Unit} {loop : Option LoopCtx}
    {origin : OriginId} {condition : Expr} {yes : Core.Block}
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before)
    (conditions : ∀ {input output : LS} {value : ValueId}, GeneratedBuilderState input →
      lowerExpr condition le input = (value,output) → NewPermissionInstructions module func le first input output)
    (yesBranch : ∀ {input output : LS} {value : ValueId}, GeneratedBuilderState input →
      LoopBuilderFrames loop input → lowerBlock loop [] false yes le input = (value,output) →
      NewPermissionInstructions module func le first input output)
    (run : lowerStmt loop (.ifS condition yes none origin) le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerStmt,bind_eq] at run
  obtain ⟨cv,conditionAfter,conditionRun,run⟩ := run
  have conditionRules := conditions generated conditionRun
  have conditionGenerated := generated.lowerExpr condition conditionRun
  have conditionFrames := frames.mono (advB_lowerExpr condition le before cv conditionAfter conditionRun).ext
  cases live : conditionAfter.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at run
    obtain ⟨_,rfl⟩ := Prod.mk.inj run
    exact conditionRules
  | some current =>
    rw [whenLive_some _ _ _ live] at run
    simp only [bind_eq] at run
    obtain ⟨⟨yesId,joinId⟩,forked,forkRun,ignored,yesInput,yesEntry,
      yesValue,yesAfter,yesRun,ignored,closed,backRun,entry⟩ := run
    have forkedGenerated := conditionGenerated.fork cv forkRun
    have forkedFrames := conditionFrames.mono (advB_fork cv le conditionAfter (yesId,joinId) forked forkRun).ext
    have ids := fork_ids forkRun
    have yesBound : yesId < forked.blocks.size := by
      have same := congrArg Prod.fst ids.1
      dsimp only at same
      rw [same,ids.2]
      nat_omega
    have yesGenerated := forkedGenerated.setCur (some yesId)
      (by intro block same; cases same; exact yesBound) yesEntry
    have yesFrames := forkedFrames.of_blocks (setCur_blocks yesEntry)
    have yesAfterGenerated := yesGenerated.lowerBlock loop [] false yes yesFrames.toTargets yesRun
    have retainedYes : ∀ instruction, FreshPermissionInstruction module func le first yesAfter instruction →
        FreshPermissionInstruction module func le first after instruction := by
      intro instruction permitted
      have extended := (advB_lowerBlock loop [] false yes le yesInput yesValue yesAfter yesRun).ext
      obtain ⟨join,joinAt,joinParams⟩ := (fork_emptyRows forkRun).2
      have inputRow : yesInput.blocks[joinId]? = some join := by
        rw [setCur_blocks yesEntry]
        exact joinAt
      obtain ⟨endJoin,endAt,endParams,_⟩ := extended.2 joinId join inputRow
      have closedPermission := permitted.emitTerm_before yesAfterGenerated.dense yesAfterGenerated.live backRun
        (by
          intro edge member destination destinationAt param paramIn
          simp only [Term.permissionEdges,List.mem_singleton] at member
          subst edge
          have row : (permissionFunc le yesAfter).blocks[joinId]? =
              some ⟨endJoin.params,endJoin.insts.toList⟩ := by
            simp only [permissionFunc,Array.getElem?_map,endAt,Option.map_some]
          rw [row] at destinationAt
          cases Option.some.inj destinationAt
          simp only [endParams,joinParams,List.not_mem_nil] at paramIn)
      exact closedPermission.setCur entry
    have retainedFork : ∀ instruction, FreshPermissionInstruction module func le first forked instruction →
        FreshPermissionInstruction module func le first after instruction := by
      intro instruction permitted
      have afterYes := (permitted.setCur yesEntry).of_framed_run yesRun
        (dense_lowerBlock loop [] false yes) (advB_lowerBlock loop [] false yes)
        (types_lowerBlock loop [] false yes) (generatedTargetFrame_lowerBlock loop [] false yes)
        yesGenerated yesFrames
      exact retainedYes instruction afterYes
    have retainedCondition : ∀ instruction,
        FreshPermissionInstruction module func le first conditionAfter instruction →
        FreshPermissionInstruction module func le first after instruction := by
      intro instruction permitted
      exact retainedFork instruction (permitted.of_framed_run forkRun (dense_fork cv)
        (advB_fork cv) (types_fork cv) (generatedTargetFrame_fork none cv) conditionGenerated trivial)
    have yesRules := (yesBranch yesGenerated yesFrames yesRun).prepend_setCur yesEntry
    intro instruction member
    rcases (NewPermissionInstructions.branch backRun).append_setCur entry instruction member with old | issued
    · rcases yesRules instruction old with old | issued
      · rcases NewPermissionInstructions.fork forkRun instruction old with old | issued
        · exact (conditionRules instruction old).imp id (retainedCondition instruction)
        · exact Or.inr (retainedFork instruction issued)
      · exact Or.inr (retainedYes instruction issued)
    · exact Or.inr issued

end Goose.Lower.Validation
