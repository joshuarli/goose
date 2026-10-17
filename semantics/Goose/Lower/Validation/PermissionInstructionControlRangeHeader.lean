import Goose.Lower.Validation.PermissionInstructionControlRange

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem newBlock_insts {le : LEnv} {before after : LS} {types : List VTy}
    {result : BlockId × List ValueId} (run : newBlock types le before = (result,after)) :
    after.insts = before.insts := by
  rw [newBlock_run_general] at run
  obtain ⟨_,rfl⟩ := Prod.mk.inj run
  simp [LS.insts]

private theorem branch_instructions_final {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after final : LS} {result : Unit} {target : BlockId} {arguments : List ValueId}
    (run : emitTerm (.br target arguments) le before = (result,after)) :
    ∀ instruction ∈ after.insts, instruction ∈ before.insts ∨
      FreshPermissionInstruction module func le first final instruction := by
  cases current : before.cur with
  | none =>
    rw [emitTerm_none _ le current] at run
    obtain ⟨_,rfl⟩ := Prod.mk.inj run
    exact fun _ member => Or.inl member
  | some block =>
    rw [emitTerm_run _ le current] at run
    obtain ⟨_,rfl⟩ := Prod.mk.inj run
    intro instruction member
    rcases permission_appendInst_membership (before := before) (block := block)
        (added := .term (.br target arguments)) member with old | rfl
    · exact Or.inl old
    · exact Or.inr (.branch module func le first final target arguments)

theorem header1_newPermissionInstructions {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : Unit} {hint : IntTy} {initial : ValueId}
    {tail : BlockId → ValueId → B Unit}
    (generated : GeneratedBuilderState before) (lower : first ≤ before.vals.size)
    (tailNew : ∀ header counter input output,
      GeneratedBuilderState input → first ≤ input.vals.size →
      (∃ block, input.blocks[header]? = some block ∧ block.params = [(counter,.data (.int hint))]) →
      before.Ext input → before.vals.size ≤ input.vals.size → TypePrefix before input →
      TermEdgesFramed none before input → tail header counter le input = ((),output) → NewPermissionInstructions module func le first input output)
    (run : (do
      let (header,ids) ← newBlock [.data (.int hint)]
      let counter := ids.headD 0
      emitTerm (.br header [initial])
      setCur (some header)
      tail header counter) le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  cases result
  simp only [bind_eq] at run
  obtain ⟨⟨header,ids⟩,allocated,allocation,ignored,branched,branchRun,ignored',selected,selectedRun,tailRun⟩ := run
  have allocatedGenerated := generated.newBlock [.data (.int hint)] allocation
  obtain ⟨head,headRow,headParams⟩ := newBlock_params allocation
  have idsEq : ids = [before.vals.size] := by
    rw [newBlock_run_general] at allocation
    simpa [paramIds] using (congrArg Prod.snd (Prod.mk.inj allocation).1).symm
  have headerBound : header < allocated.blocks.size := (Array.getElem?_eq_some_iff.mp headRow).1
  have branchedGenerated := allocatedGenerated.emitTerm _ (by
    intro target member
    simp only [Term.successors,List.mem_singleton] at member
    subst target
    exact headerBound) branchRun
  have branchedBound := Nat.lt_of_lt_of_le headerBound (adv_emitTerm branchRun).ext.1
  have selectedGenerated := branchedGenerated.setCur (some header)
    (by intro block same; cases same; exact branchedBound) selectedRun
  have selectedGrowth : before.vals.size ≤ selected.vals.size := by
    have grows := (adv_newBlock1 allocation).vals
    have afterBranch := (adv_emitTerm branchRun).vals
    rw [setCur_run] at selectedRun
    obtain ⟨_,rfl⟩ := Prod.mk.inj selectedRun
    exact Nat.le_trans grows afterBranch
  have selectedLower := Nat.le_trans lower selectedGrowth
  obtain ⟨selectedHead,selectedHeadRow,selectedHeadParams,_⟩ :=
    (adv_emitTerm branchRun).ext.2 header head headRow
  have headerAt : ∃ block, selected.blocks[header]? = some block ∧
      block.params = [(ids.headD 0,.data (.int hint))] := by
    refine ⟨selectedHead,?_,?_⟩
    · rw [setCur_blocks selectedRun]; exact selectedHeadRow
    · rw [selectedHeadParams,headParams,idsEq]
      rfl
  have allocationFramed := generatedTargetFrame_newBlock none [.data (.int hint)]
    before le before (header,ids) allocated (.refl _) trivial (.refl _ _) allocation
  have headerFresh := newBlock_fresh (LS.Ext.refl before) allocation
  have branchFramed := allocationFramed.1.emitTermAt branchRun (by
    intro target member old
    simp only [Term.successors,List.mem_singleton] at member
    subst target
    exact False.elim (Nat.not_lt_of_ge headerFresh old))
  have prefixExt := (adv_newBlock1 allocation).ext.trans (adv_emitTerm branchRun).ext
  have selectedFramed := generatedTargetFrame_setCur none (some header) before le branched ignored' selected
    prefixExt trivial branchFramed selectedRun
  have selectedTypes := (types_newBlock _ le before (header,ids) allocated allocation).trans
    ((types_emitTerm _ le allocated ignored branched branchRun).trans
      (types_setCur _ le branched ignored' selected selectedRun))
  have tailRules := tailNew header (ids.headD 0) selected after selectedGenerated selectedLower headerAt
    (prefixExt.trans selectedFramed.2) selectedGrowth selectedTypes selectedFramed.1 tailRun
  intro instruction member
  rcases tailRules instruction member with old | fresh
  · have branchedMember : instruction ∈ branched.insts := by
      rw [setCur_run] at selectedRun
      obtain ⟨_,rfl⟩ := Prod.mk.inj selectedRun
      exact old
    rcases branch_instructions_final branchRun instruction branchedMember with original | issued
    · exact Or.inl (by simpa only [newBlock_insts allocation] using original)
    · exact Or.inr issued
  · exact Or.inr fresh

#print axioms header1_newPermissionInstructions

end Goose.Lower.Validation
