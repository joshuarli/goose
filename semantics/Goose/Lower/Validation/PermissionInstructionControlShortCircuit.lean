import Goose.Lower.Validation.PermissionInstructionControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem newBlock_insts {le : LEnv} {before after : LS} {types : List VTy}
    {result : BlockId × List ValueId} (run : Goose.Lower.newBlock types le before = (result,after)) :
    after.insts = before.insts := by
  rw [newBlock_run_general] at run
  obtain ⟨_,rfl⟩ := Prod.mk.inj run
  simp [LS.insts]

private theorem conditional_instructions {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after final : LS} {result : Unit} {condition : ValueId}
    {yes no : BlockId} {yesArgs noArgs : List ValueId}
    (run : emitTerm (.condbr condition yes yesArgs no noArgs) le before = (result,after)) :
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
        (added := .term (.condbr condition yes yesArgs no noArgs)) member with old | rfl
    · exact Or.inl old
    · exact Or.inr (FreshPermissionInstruction.conditional module func le first final condition yes yesArgs no noArgs)

private theorem scFork_instructions {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after final : LS} {result : BlockId × BlockId × ValueId}
    {condition : ValueId} {isAnd : Bool}
    (run : scFork isAnd condition le before = (result,after)) :
    ∀ instruction ∈ after.insts, instruction ∈ before.insts ∨
      FreshPermissionInstruction module func le first final instruction := by
  cases isAnd <;> simp only [scFork,Bool.false_eq_true,ite_false,ite_true,bind_eq] at run
  all_goals
    obtain ⟨rhs,one,rhsRun,join,two,joinRun,ignored,three,branchRun,finish⟩ := run
    rw [pure_run] at finish
    obtain ⟨_,rfl⟩ := Prod.mk.inj finish
    intro instruction member
    rcases conditional_instructions branchRun instruction member with old | fresh
    · exact Or.inl (by simpa only [newBlock_insts joinRun,newBlock_insts rhsRun] using old)
    · exact Or.inr fresh

theorem shortCircuit_newPermissionInstructions {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result condition : ValueId} {isAnd : Bool} {rhs : B ValueId}
    (generated : GeneratedBuilderState before) (lower : first ≤ before.vals.size)
    (rhsDense : DenseRun rhs) (rhsAdvance : AdvB rhs)
    (rhsNew : ∀ input value output, GeneratedBuilderState input → rhs le input = (value,output) →
      NewPermissionInstructions module func le input.vals.size input output)
    (run : shortCircuit isAnd condition rhs le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  cases current : before.cur with
  | none =>
    rw [shortCircuit,whenLive_none _ _ le current] at run
    obtain ⟨_,rfl⟩ := Prod.mk.inj run
    exact NewPermissionInstructions.of_blocks_eq rfl
  | some source =>
    rw [shortCircuit,whenLive_some _ _ le current] at run
    simp only [bind_eq] at run
    obtain ⟨⟨rhsBlock,join,parameter⟩,forked,forkRun,ignored,selected,selectedRun,
      value,body,bodyRun,ignored',closed,closedRun,ignored'',final,finalRun,finish⟩ := run
    rw [pure_run] at finish
    obtain ⟨_,rfl⟩ := Prod.mk.inj finish
    obtain ⟨ids,size⟩ := scFork_ids forkRun
    have forkGenerated := generated.scFork isAnd condition forkRun
    have rhsBound : rhsBlock < forked.blocks.size := by
      have same := congrArg Prod.fst ids
      dsimp only at same
      rw [same,size]
      exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
    have selectedGenerated := forkGenerated.setCur (some rhsBlock) (by
      intro block same
      cases Option.some.inj same
      exact rhsBound) selectedRun
    have joinBound : join < selected.blocks.size := by
      rw [setCur_blocks selectedRun]
      have same := congrArg (fun value => value.2.1) ids
      dsimp only at same
      rw [same,size]
      exact Nat.add_lt_add_left (by decide : 1 < 2) _
    have child := rhsNew selected value body selectedGenerated bodyRun
    have bodyDense := rhsDense le selected value body bodyRun selectedGenerated.dense selectedGenerated.live
    have bodyAdvance := rhsAdvance le selected value body bodyRun
    have oldTarget : ∀ edge ∈ (Term.br join [value]).permissionEdges, ∀ destination,
        (permissionFunc le body).blocks[edge.1]? = some destination →
        ∀ param ∈ destination.params, param.1 < selected.vals.size := by
      intro edge member destination row param belongs
      have same : edge = (join,[value]) := by simpa [Term.permissionEdges] using member
      subst edge
      obtain ⟨old,oldRow,params⟩ := permissionFunc_old_target bodyAdvance.ext joinBound row
      apply permissionFunc_param_bound selectedGenerated.dense
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? oldRow))
      rw [← params]
      exact belongs
    have closedNew : NewPermissionInstructions module func le selected.vals.size selected closed := by
      apply child.compose (NewPermissionInstructions.branch closedRun)
      intro instruction member permitted
      exact permitted.emitTerm_before bodyDense.1 bodyDense.2.1 closedRun oldTarget
    have lowerSelected : first ≤ selected.vals.size := by
      have grows := (advB_scFork isAnd condition le before _ forked forkRun).vals
      rw [setCur_run] at selectedRun
      obtain ⟨_,rfl⟩ := Prod.mk.inj selectedRun
      exact Nat.le_trans lower grows
    have tail := NewPermissionInstructions.append_setCur (closedNew.weaken lowerSelected) finalRun
    intro instruction member
    rcases tail instruction member with old | fresh
    · have forkMember : instruction ∈ forked.insts := by
        rw [setCur_run] at selectedRun
        obtain ⟨_,rfl⟩ := Prod.mk.inj selectedRun
        exact old
      exact scFork_instructions forkRun instruction forkMember
    · exact Or.inr fresh

#print axioms shortCircuit_newPermissionInstructions

end Goose.Lower.Validation
