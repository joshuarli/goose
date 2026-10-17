import Goose.Lower.Validation.EmittedMetadataStatic

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem EmittedStatic.of_blocks_eq {module : Core.Module} {before after : LS}
    (checked : EmittedStatic module before) (same : after.blocks = before.blocks) :
    EmittedStatic module after := by
  constructor
  · simpa only [LS.insts, same] using checked.profiles
  · constructor
    · simpa only [same] using checked.resolved.parameters
    · simpa only [LS.insts, same] using checked.resolved.annotations

theorem EmittedStaticRun.of_blocks_eq {module : Core.Module} {le : LEnv} {action : B α}
    (unchanged : ∀ before, (action le before).2.blocks = before.blocks) :
    EmittedStaticRun module le action := by
  intro before result after run checked
  apply checked.of_blocks_eq
  simpa only [run] using unchanged before

theorem static_emitDef {module : Core.Module} {le : LEnv} (op : Op)
    (profile : ∀ value, EmittedProfileInst module.profile (.def value op))
    (annotation : ∀ value, EmittedAnnotationResolved module (.def value op)) :
    EmittedStaticRun module le (emitDef op) := by
  intro before result after run checked
  cases live : before.cur with
  | none =>
    rw [emitDef_none op le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitDef_run op le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact (checked.appendInst block (.def before.vals.size op)
      (profile _) (annotation _)).of_blocks_eq rfl

theorem static_emitEffect {module : Core.Module} {le : LEnv} (effect : Effect)
    (profile : EmittedProfileInst module.profile (.eff effect)) :
    EmittedStaticRun module le (emitEffect effect) := by
  intro before result after run checked
  cases live : before.cur with
  | none =>
    rw [emitEffect_none effect le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitEffect_run effect le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked.appendInst block (.eff effect) profile trivial

theorem static_emitTerm {module : Core.Module} {le : LEnv} (term : Term)
    (profile : EmittedProfileInst module.profile (.term term)) :
    EmittedStaticRun module le (emitTerm term) := by
  intro before result after run checked
  cases live : before.cur with
  | none =>
    rw [emitTerm_none term le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitTerm_run term le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact (checked.appendInst block (.term term) profile trivial).of_blocks_eq rfl

theorem static_patchTerm {module : Core.Module} {le : LEnv} (block : BlockId) (term : Term)
    (profile : EmittedProfileInst module.profile (.term term)) :
    EmittedStaticRun module le (patchTerm block term) := by
  intro before result after run checked
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact checked.appendInst block (.term term) profile trivial

theorem static_newBlock {module : Core.Module} {le : LEnv} (types : List VTy)
    (resolved : ∀ type ∈ types, EmittedVTyResolved module type) :
    EmittedStaticRun module le (newBlock types) := by
  intro before result after run checked
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  apply checked.of_transport
  · intro block member parameter parameterAt
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact Or.inl ⟨block, old, parameterAt⟩
    · exact Or.inr (resolved parameter.2 (List.of_mem_zip parameterAt).2)
  · intro inst member
    exact Or.inl (by simpa [LS.insts] using member)

theorem static_setCur (module : Core.Module) (le : LEnv) (current : Option BlockId) :
    EmittedStaticRun module le (setCur current) := by
  apply EmittedStaticRun.of_blocks_eq
  intro before
  rw [setCur_run]

theorem static_get (module : Core.Module) (le : LEnv) :
    EmittedStaticRun module le (get : B LS) := by
  exact EmittedStaticRun.of_blocks_eq (fun _ => rfl)

theorem static_read (module : Core.Module) (le : LEnv) :
    EmittedStaticRun module le (read : B LEnv) := by
  exact EmittedStaticRun.of_blocks_eq (fun _ => rfl)

theorem static_valTy (module : Core.Module) (le : LEnv) (value : ValueId) :
    EmittedStaticRun module le (valTy value) := by
  exact EmittedStaticRun.of_blocks_eq (fun before => by rw [valTy_run])

theorem static_curBlock (module : Core.Module) (le : LEnv) :
    EmittedStaticRun module le curBlock := by
  exact EmittedStaticRun.of_blocks_eq (fun before => by rw [curBlock_run])

theorem static_pushScope (module : Core.Module) (le : LEnv) (scope : ScopeId) :
    EmittedStaticRun module le (pushScope scope) := by
  exact EmittedStaticRun.of_blocks_eq (fun before => by rw [pushScope_run])

theorem static_popScope (module : Core.Module) (le : LEnv) :
    EmittedStaticRun module le popScope := by
  exact EmittedStaticRun.of_blocks_eq (fun before => by rw [popScope_run])

end Goose.Lower.Validation
