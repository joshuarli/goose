import Goose.Lower.Validation.PermissionPreservationState

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem permission_appendInst_membership {before : LS} {block : BlockId} {added instruction : Inst}
    (member : instruction ∈ (before.appendInst block added).insts) :
    instruction ∈ before.insts ∨ instruction = added := by
  simp only [LS.insts, LS.appendInst, Array.toList_modify] at member
  obtain ⟨actual, blockMember, instructionMember⟩ := List.mem_flatMap.mp member
  rcases list_mem_modify_cases _ _ _ blockMember with old | ⟨original, originalMember, shape⟩
  · exact Or.inl (List.mem_flatMap.mpr ⟨actual, old, instructionMember⟩)
  · subst actual
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at instructionMember
    rcases instructionMember with old | same
    · exact Or.inl (List.mem_flatMap.mpr ⟨original, originalMember, old⟩)
    · exact Or.inr same

theorem PermissionState.emitDef {module : GIR.Module} {func : Func} {le : LEnv}
    {before after : LS} {value : ValueId} {op : Op}
    (permitted : PermissionState module func le before)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : emitDef op le before = (value, after))
    (issued : before.cur.isSome = true → PermissionInstruction module func le after (.def value op)) :
    PermissionState module func le after := by
  have retained := permitted.of_framed_run run (dense_emitDef op) (advB_emitDef op)
    (types_emitDef op) (generatedTargetFrame_emitDef none op) checked bounded (by trivial)
  cases current : before.cur with
  | none =>
    rw [emitDef_none op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact permitted
  | some block =>
    rw [emitDef_run op le current] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    intro instruction member
    have original := permission_appendInst_membership (before := before) (block := block) (added := (.def before.vals.size op)) member
    rcases original with old | same
    · exact retained instruction old
    · subst instruction
      exact issued (by simp [current])

theorem PermissionState.emitEffect {module : GIR.Module} {func : Func} {le : LEnv}
    {before after : LS} {result : Unit} {effect : Effect}
    (permitted : PermissionState module func le before)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : emitEffect effect le before = (result, after))
    (issued : before.cur.isSome = true → PermissionInstruction module func le after (.eff effect)) :
    PermissionState module func le after := by
  have retained := permitted.of_framed_run run (dense_emitEffect effect) (advB_emitEffect effect)
    (types_emitEffect effect) (generatedTargetFrame_emitEffect none effect) checked bounded (by trivial)
  cases current : before.cur with
  | none =>
    rw [emitEffect_none effect le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact permitted
  | some block =>
    rw [emitEffect_run effect le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    intro instruction member
    have original := permission_appendInst_membership (before := before) (block := block) (added := (.eff effect)) member
    rcases original with old | same
    · exact retained instruction old
    · subst instruction
      exact issued (by simp [current])

theorem PermissionState.emitNoSuccessors {module : GIR.Module} {func : Func} {le : LEnv}
    {before after : LS} {result : Unit} {term : Term}
    (permitted : PermissionState module func le before)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (successors : term.successors = [])
    (run : emitTerm term le before = (result, after))
    (issued : before.cur.isSome = true → PermissionInstruction module func le after (.term term)) :
    PermissionState module func le after := by
  have retained := permitted.of_framed_run run (dense_emitTerm term) (advB_emitTerm term)
    (types_emitTerm term) (generatedTargetFrame_emitNoSuccessors none term successors) checked bounded (by trivial)
  cases current : before.cur with
  | none =>
    rw [emitTerm_none term le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact permitted
  | some block =>
    rw [emitTerm_run term le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    intro instruction member
    have original := permission_appendInst_membership (before := before) (block := block) (added := (.term term)) member
    rcases original with old | same
    · exact retained instruction old
    · subst instruction
      exact issued (by simp [current])

#print axioms PermissionState.emitDef
#print axioms PermissionState.emitEffect
#print axioms PermissionState.emitNoSuccessors

end Goose.Lower.Validation
