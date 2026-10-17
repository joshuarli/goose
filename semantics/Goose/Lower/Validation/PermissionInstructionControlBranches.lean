import Goose.Lower.Validation.PermissionInstructionControl
import Goose.Lower.Validation.PermissionInstructionControlGraphJoin

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem FreshPermissionInstruction.recordValueRootRecipe {module : GIR.Module} {func : Func}
    {le : LEnv} {first : Nat} {before after : LS} {value : ValueId} {result : Unit}
    {instruction : Inst} {sourceScope : ScopeId}
    (permitted : FreshPermissionInstruction module func le first before instruction)
    (run : recordValueRootRecipe value sourceScope le before = (result, after)) :
    FreshPermissionInstruction module func le first after instruction := by
  rw [recordValueRootRecipe_run] at run
  obtain ⟨_, stateEq⟩ := Prod.mk.inj run
  have sameFunc : permissionFunc le after = permissionFunc le before := by
    rw [← stateEq]
    rfl
  have sameValues : after.vals = before.vals := by
    rw [← stateEq]
  have sameWritable : FreshWritableEvidence le first after = FreshWritableEvidence le first before := by
    funext candidate
    apply propext
    constructor
    · intro evidence
      obtain ⟨writable, contents, closed, elements, bindingParameters, contentParameters,
        member, freshWritable, freshContents⟩ := evidence
      exact ⟨writable, contents,
        by simpa only [sameFunc, sameValues] using closed,
        by simpa only [sameFunc, sameValues] using elements,
        by simpa only [sameFunc] using bindingParameters,
        by simpa only [sameFunc] using contentParameters,
        member, freshWritable, freshContents⟩
    · intro evidence
      obtain ⟨writable, contents, closed, elements, bindingParameters, contentParameters,
        member, freshWritable, freshContents⟩ := evidence
      exact ⟨writable, contents,
        by simpa only [sameFunc, sameValues] using closed,
        by simpa only [sameFunc, sameValues] using elements,
        by simpa only [sameFunc] using bindingParameters,
        by simpa only [sameFunc] using contentParameters,
        member, freshWritable, freshContents⟩
  have sameContents : FreshContentsEvidence le first after = FreshContentsEvidence le first before := by
    funext candidate
    apply propext
    constructor
    · intro evidence
      obtain ⟨authorized, closed, parameters, member, fresh⟩ := evidence
      exact ⟨authorized,
        by simpa only [sameFunc, sameValues] using closed,
        by simpa only [sameFunc] using parameters,
        member, fresh⟩
    · intro evidence
      obtain ⟨authorized, closed, parameters, member, fresh⟩ := evidence
      exact ⟨authorized,
        by simpa only [sameFunc, sameValues] using closed,
        by simpa only [sameFunc] using parameters,
        member, fresh⟩
  change PermissionRule module func after.vals (FreshWritableEvidence le first after)
      (FreshContentsEvidence le first after) instruction ∧ PermissionGuardTypes after.vals instruction
  rw [sameWritable, sameContents, sameValues]
  exact permitted

private theorem NewPermissionInstructions.recordValueRootRecipe {module : GIR.Module} {func : Func}
    {le : LEnv} {first : Nat} {before after : LS} {value : ValueId} {result : Unit}
    {sourceScope : ScopeId}
    (run : recordValueRootRecipe value sourceScope le before = (result, after)) :
    NewPermissionInstructions module func le first before after := by
  apply NewPermissionInstructions.of_blocks_eq
  rw [recordValueRootRecipe_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  rfl

private theorem patchBrs_instruction_cases {le : LEnv} {target : BlockId} :
    ∀ (incoming : List (BlockId × ValueId)) {before after : LS} {result : Unit},
      patchBrs target incoming le before = (result,after) → ∀ instruction ∈ after.insts,
      instruction ∈ before.insts ∨ ∃ value, instruction = .term (.br target [value]) := by
  intro incoming
  induction incoming with
  | nil =>
    intro before after result run instruction member
    simp only [patchBrs,pure_run] at run
    obtain ⟨_,rfl⟩ := Prod.mk.inj run
    exact Or.inl member
  | cons pair rest induction =>
    intro before after result run instruction member
    simp only [patchBrs,bind_eq] at run
    obtain ⟨ignored,middle,patched,finished⟩ := run
    rcases induction finished instruction member with old | added
    · rw [patchTerm_run] at patched
      obtain ⟨_,rfl⟩ := Prod.mk.inj patched
      rcases permission_appendInst_membership (before := before) (block := pair.1)
          (added := .term (.br target [pair.2])) old with original | same
      · exact Or.inl original
      · exact Or.inr ⟨pair.2,same⟩
    · exact Or.inr added

theorem NewPermissionInstructions.patchBrs {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : Unit} {target : BlockId}
    {incoming : List (BlockId × ValueId)}
    (run : Goose.Lower.patchBrs target incoming le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  intro instruction member
  rcases patchBrs_instruction_cases incoming run instruction member with old | ⟨value,rfl⟩
  · exact Or.inl old
  · exact Or.inr (FreshPermissionInstruction.branch module func le first after target [value])

theorem NewPermissionInstructions.joinValue {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result yesValue noValue : ValueId} {yes no : Option BlockId}
    (run : Goose.Lower.joinValue yes yesValue no noValue le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  unfold Goose.Lower.joinValue at run
  split at run
  · simp only [bind_eq,setCur_run] at run
    obtain ⟨ignored,entered,entry,finish⟩ := run
    obtain ⟨_,rfl⟩ := Prod.mk.inj entry
    rw [pure_run] at finish
    obtain ⟨_,rfl⟩ := Prod.mk.inj finish
    exact .of_blocks_eq rfl
  · simp only [bind_eq] at run
    obtain ⟨ty,typed,typeRun,join,allocated,allocation,patched,middle,patchRun,
      ignored,entered,entry,finish⟩ := run
    have typedSame : typed = before := by
      have same := valTy_run
        (((yes.map fun b => (b,yesValue)).toList ++ (no.map fun b => (b,noValue)).toList).headD (0,0)).2 le before
      rw [typeRun] at same
      exact same
    subst typed
    rw [pure_run] at finish
    obtain ⟨_,rfl⟩ := Prod.mk.inj finish
    exact (NewPermissionInstructions.patchBrs patchRun).append_setCur entry |>.prepend_newBlock allocation

theorem lowerIf_newPermissionInstructions {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : ValueId} {condition : Expr} {yes no : Core.Block}
    (generated : GeneratedBuilderState before) (floor : first ≤ before.vals.size)
    (conditions : ∀ {input output : LS} {value : ValueId}, GeneratedBuilderState input → first ≤ input.vals.size →
      lowerExpr condition le input = (value,output) → NewPermissionInstructions module func le first input output)
    (yesBranch : ∀ {input output : LS} {value : ValueId}, GeneratedBuilderState input → first ≤ input.vals.size →
      lowerBlock none [] true yes le input = (value,output) → NewPermissionInstructions module func le first input output)
    (noBranch : ∀ {input output : LS} {value : ValueId}, GeneratedBuilderState input → first ≤ input.vals.size →
      lowerBlock none [] true no le input = (value,output) → NewPermissionInstructions module func le first input output)
    (run : lowerExpr (.ifE condition yes no) le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerExpr,bind_eq] at run
  obtain ⟨cv,conditionAfter,conditionRun,run⟩ := run
  have conditionRules := conditions generated floor conditionRun
  have conditionGenerated := generated.lowerExpr condition conditionRun
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
    rcases joining with ⟨joinedValue, joinedState, joinRun, recipe⟩
    rcases recipe with ⟨recipeResult, recipeState, recipeRun, pureRun⟩
    rw [pure_run] at pureRun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pureRun
    have joinedInstructions : NewPermissionInstructions module func le first noRead joinedState :=
      NewPermissionInstructions.joinValue joinRun
    have recipeInstructions : NewPermissionInstructions module func le first joinedState recipeState :=
      NewPermissionInstructions.recordValueRootRecipe recipeRun
    have retainedRecipe : ∀ instruction ∈ joinedState.insts,
        FreshPermissionInstruction module func le first joinedState instruction →
        FreshPermissionInstruction module func le first recipeState instruction := by
      intro instruction member permitted
      exact permitted.recordValueRootRecipe recipeRun
    have joiningInstructions := joinedInstructions.compose recipeInstructions retainedRecipe
    rw [curBlock_run] at yesReadRun noReadRun
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj yesReadRun
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj noReadRun
    have forkedGenerated := conditionGenerated.fork cv forkRun
    have forkedFloor := Nat.le_trans floor (Nat.le_trans (advB_lowerExpr condition le before cv conditionAfter conditionRun).vals
      (advB_fork cv le conditionAfter _ forked forkRun).vals)
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
    have yesFloor : first ≤ yesInput.vals.size := by
      have same := yesEntry
      rw [setCur_run] at same
      obtain ⟨_,rfl⟩ := Prod.mk.inj same
      exact forkedFloor
    have yesGenerated := forkedGenerated.setCur (some yesId)
      (by intro block same; cases same; exact yesBound) yesEntry
    have yesAfterGenerated := yesGenerated.lowerBlock none [] true yes trivial yesRun
    have noTarget : noId < yesAfter.blocks.size := by
      have growth := (advB_lowerBlock none [] true yes le yesInput yesValue yesAfter yesRun).ext.1
      rw [setCur_blocks yesEntry] at growth
      exact Nat.lt_of_lt_of_le noBound growth
    have noFloor : first ≤ noInput.vals.size := by
      have same := noEntry
      rw [setCur_run] at same
      obtain ⟨_,rfl⟩ := Prod.mk.inj same
      exact Nat.le_trans yesFloor (advB_lowerBlock none [] true yes le yesInput yesValue yesAfter yesRun).vals
    have noGenerated := yesAfterGenerated.setCur (some noId)
      (by intro block same; cases same; exact noTarget) noEntry
    have noAfterGenerated := noGenerated.lowerBlock none [] true no trivial noRun
    have retainedYes : ∀ instruction, FreshPermissionInstruction module func le first yesAfter instruction →
        FreshPermissionInstruction module func le first recipeState instruction := by
      intro instruction permitted
      have atNo := permitted.setCur noEntry
      have afterNo := atNo.of_framed_run noRun (dense_lowerBlock none [] true no)
        (advB_lowerBlock none [] true no) (types_lowerBlock none [] true no)
        (generatedTargetFrame_lowerBlock none [] true no) noGenerated trivial
      exact (afterNo.joinValue noAfterGenerated.dense noAfterGenerated.live joinRun).recordValueRootRecipe
        recipeRun
    have retainedFork : ∀ instruction, FreshPermissionInstruction module func le first forked instruction →
        FreshPermissionInstruction module func le first recipeState instruction := by
      intro instruction permitted
      have atYes := permitted.setCur yesEntry
      have afterYes := atYes.of_framed_run yesRun (dense_lowerBlock none [] true yes)
        (advB_lowerBlock none [] true yes) (types_lowerBlock none [] true yes)
        (generatedTargetFrame_lowerBlock none [] true yes) yesGenerated trivial
      exact retainedYes instruction afterYes
    have retainedCondition : ∀ instruction,
        FreshPermissionInstruction module func le first conditionAfter instruction →
        FreshPermissionInstruction module func le first recipeState instruction := by
      intro instruction permitted
      exact retainedFork instruction (permitted.of_framed_run forkRun (dense_fork cv)
        (advB_fork cv) (types_fork cv) (generatedTargetFrame_fork none cv) conditionGenerated trivial)
    have yesRules := (yesBranch yesGenerated yesFloor yesRun).prepend_setCur yesEntry
    have noRules := (noBranch noGenerated noFloor noRun).prepend_setCur noEntry
    intro instruction member
    rcases joiningInstructions instruction member with old | issued
    · rcases noRules instruction old with old | issued
      · rcases yesRules instruction old with old | issued
        · rcases NewPermissionInstructions.fork forkRun instruction old with old | issued
          · exact (conditionRules instruction old).imp id (retainedCondition instruction)
          · exact Or.inr (retainedFork instruction issued)
        · exact Or.inr (retainedYes instruction issued)
      · exact Or.inr ((issued.joinValue noAfterGenerated.dense noAfterGenerated.live joinRun).recordValueRootRecipe
          recipeRun)
    · exact Or.inr issued

end Goose.Lower.Validation
