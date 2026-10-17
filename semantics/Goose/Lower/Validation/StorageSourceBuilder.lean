import Goose.Lower.Validation.StorageSourceRules
import Goose.Lower.GeneratedBuilder
import Goose.Lower.Validation.EmittedTypingTrace

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def StorageBuilder (profile : ArtifactProfile) (state : LS) : Prop :=
  ∀ instruction ∈ state.insts, StorageAuthority profile state.vals instruction

theorem StorageBuilder.retained {profile : ArtifactProfile} {before after : LS}
    (checked : StorageBuilder profile before) (types : TypePrefix before after)
    (instructions : ∀ instruction ∈ after.insts, instruction ∈ before.insts) : StorageBuilder profile after := by
  intro instruction member
  exact (checked instruction (instructions instruction member)).retained types

theorem storageInstruction_appendInst {before : LS} {block : BlockId} {instruction appended : Inst}
    (member : instruction ∈ (before.appendInst block appended).insts) :
    instruction ∈ before.insts ∨ instruction = appended := by
  obtain ⟨body, bodyMember, instMember⟩ := List.mem_flatMap.mp member
  obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp bodyMember)
  change (before.blocks.modify block fun body => { body with insts := body.insts.push appended })[index]? = some body at lookup
  rw [Array.getElem?_modify] at lookup
  by_cases same : block = index
  · simp only [same, ↓reduceIte] at lookup
    cases oldRow : before.blocks[index]? with
    | none => simp [oldRow] at lookup
    | some old =>
      simp only [oldRow, Option.map_some, Option.some.injEq] at lookup
      subst body
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at instMember
      rcases instMember with previous | fresh
      · exact Or.inl (List.mem_flatMap.mpr ⟨old, Array.mem_toList_iff.mpr (Array.mem_of_getElem? oldRow), previous⟩)
      · exact Or.inr fresh
  · simp only [same, ↓reduceIte] at lookup
    exact Or.inl (List.mem_flatMap.mpr ⟨body, Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup), instMember⟩)

theorem StorageBuilder.appendInst {profile : ArtifactProfile} {before : LS} {block : BlockId} {instruction : Inst}
    (checked : StorageBuilder profile before) (emitted : StorageAuthority profile before.vals instruction) :
    StorageBuilder profile (before.appendInst block instruction) := by
  intro next member
  rcases storageInstruction_appendInst member with previous | rfl
  · exact checked next previous
  · exact emitted

theorem StorageBuilder.emitDef {le : LEnv} {before after : LS} {result : ValueId} {op : Op}
    (checked : StorageBuilder le.mod.profile before)
    (emitted : ∀ value, StorageAuthority le.mod.profile before.vals (.def value op))
    (run : emitDef op le before = (result, after)) : StorageBuilder le.mod.profile after := by
  cases live : before.cur with
  | none =>
      rw [emitDef_none op le live] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      exact checked
  | some block =>
      have types := types_emitDef op le before result after run
      rw [emitDef_run op le live] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      let extended : LS := { before with vals := before.vals.push (some ((op.resultTy (tyEnv le before)).toOption.getD (.data .unit))) }
      have old : StorageBuilder le.mod.profile extended := by
        intro instruction member
        exact (checked instruction member).retained types
      exact old.appendInst ((emitted before.vals.size).retained types)

theorem StorageBuilder.emitEffect {le : LEnv} {before after : LS} {result : Unit} {effect : Effect}
    (checked : StorageBuilder le.mod.profile before)
    (emitted : StorageAuthority le.mod.profile before.vals (.eff effect))
    (run : emitEffect effect le before = (result, after)) : StorageBuilder le.mod.profile after := by
  cases live : before.cur with
  | none =>
      rw [emitEffect_none effect le live] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      exact checked
  | some block =>
      rw [emitEffect_run effect le live] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      exact checked.appendInst emitted

theorem StorageBuilder.patchTerm {le : LEnv} {before after : LS} {result : Unit}
    {block : BlockId} {term : Term} (checked : StorageBuilder le.mod.profile before)
    (run : patchTerm block term le before = (result, after)) : StorageBuilder le.mod.profile after := by
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact checked.appendInst trivial

theorem StorageBuilder.emitTerm {le : LEnv} {before after : LS} {result : Unit}
    {term : Term} (checked : StorageBuilder le.mod.profile before)
    (run : emitTerm term le before = (result, after)) : StorageBuilder le.mod.profile after := by
  cases live : before.cur with
  | none =>
      rw [emitTerm_none term le live] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      exact checked
  | some block =>
      rw [emitTerm_run term le live] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      exact checked.appendInst trivial

theorem StorageBuilder.newBlock {le : LEnv} {before after : LS} {types : List VTy}
    {result : BlockId × List ValueId} (checked : StorageBuilder le.mod.profile before)
    (run : newBlock types le before = (result, after)) : StorageBuilder le.mod.profile after := by
  apply checked.retained (types_newBlock types le before result after run)
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  intro instruction member
  simpa [LS.insts] using member

theorem StorageBuilder.finishBlocks {le : LEnv} {state : LS} {func : Func}
    (checked : StorageBuilder le.mod.profile state) (blocks : func.blocks = finishBlocks state.blocks) :
    ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      StorageRule le.mod.profile state.vals instruction := by
  intro block member instruction belongs
  rw [blocks, Goose.Lower.finishBlocks, Array.toList_map] at member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  exact (checked instruction (List.mem_flatMap.mpr ⟨source, sourceMember, belongs⟩)).rule

end Goose.Lower.Validation
