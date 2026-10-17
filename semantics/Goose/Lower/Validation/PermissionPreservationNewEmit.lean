import Goose.Lower.Validation.PermissionPreservationFreshRules
import Goose.Lower.Validation.PermissionPreservationEmit

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem NewPermissionInstructions.of_blocks_eq {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} (blocks : after.blocks = before.blocks) :
    NewPermissionInstructions module func le first before after := by
  intro instruction member
  exact Or.inl (by simpa only [LS.insts, blocks] using member)

theorem NewPermissionInstructions.emitDef {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {value : ValueId} {op : Op}
    (run : emitDef op le before = (value, after))
    (issued : before.cur.isSome = true →
      FreshPermissionInstruction module func le first after (.def value op)) :
    NewPermissionInstructions module func le first before after := by
  cases current : before.cur with
  | none =>
    rw [emitDef_none op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact .of_blocks_eq rfl
  | some block =>
    rw [emitDef_run op le current] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    intro instruction member
    rcases permission_appendInst_membership (before := before) (block := block)
        (added := .def before.vals.size op) member with old | same
    · exact Or.inl old
    · subst instruction
      exact Or.inr (issued (by simp [current]))

theorem NewPermissionInstructions.emitEffect {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : Unit} {effect : Effect}
    (run : emitEffect effect le before = (result, after))
    (issued : before.cur.isSome = true →
      FreshPermissionInstruction module func le first after (.eff effect)) :
    NewPermissionInstructions module func le first before after := by
  cases current : before.cur with
  | none =>
    rw [emitEffect_none effect le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact .of_blocks_eq rfl
  | some block =>
    rw [emitEffect_run effect le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    intro instruction member
    rcases permission_appendInst_membership (before := before) (block := block)
        (added := .eff effect) member with old | same
    · exact Or.inl old
    · subst instruction
      exact Or.inr (issued (by simp [current]))

theorem NewPermissionInstructions.emitTerm {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : Unit} {term : Term}
    (run : emitTerm term le before = (result, after))
    (issued : before.cur.isSome = true →
      FreshPermissionInstruction module func le first after (.term term)) :
    NewPermissionInstructions module func le first before after := by
  cases current : before.cur with
  | none =>
    rw [emitTerm_none term le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact .of_blocks_eq rfl
  | some block =>
    rw [emitTerm_run term le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    intro instruction member
    rcases permission_appendInst_membership (before := before) (block := block)
        (added := .term term) member with old | same
    · exact Or.inl old
    · subst instruction
      exact Or.inr (issued (by simp [current]))

theorem NewPermissionInstructions.newBlock {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : BlockId × List ValueId} {types : List VTy}
    (run : newBlock types le before = (result, after)) :
    NewPermissionInstructions module func le first before after := by
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  intro instruction member
  exact Or.inl (by simpa [LS.insts] using member)

#print axioms NewPermissionInstructions.emitDef
#print axioms NewPermissionInstructions.emitEffect
#print axioms NewPermissionInstructions.emitTerm
#print axioms NewPermissionInstructions.newBlock

end Goose.Lower.Validation
