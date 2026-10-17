import Goose.Lower.Validation.EmittedMetadataStaticSourceChecks

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def EmittedProfile (profile : ArtifactProfile) (state : LS) : Prop :=
  ∀ inst ∈ state.insts, EmittedProfileInst profile inst

def EmittedProfileRun (profile : ArtifactProfile) (le : LEnv) (action : B α) : Prop :=
  ∀ before result after, action le before = (result, after) → EmittedProfile profile before → EmittedProfile profile after

theorem EmittedProfileRun.pure {profile : ArtifactProfile} {le : LEnv} (value : α) :
    EmittedProfileRun profile le (pure value) := by
  intro before result after run checked
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact checked

theorem EmittedProfileRun.bind {profile : ArtifactProfile} {le : LEnv}
    {first : B α} {next : α → B β} (one : EmittedProfileRun profile le first)
    (two : ∀ value, EmittedProfileRun profile le (next value)) : EmittedProfileRun profile le (first >>= next) := by
  intro before result after run checked
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  exact two value middle result after nextRun (one before value middle firstRun checked)

theorem EmittedProfileRun.of_blocks_eq {profile : ArtifactProfile} {le : LEnv} {action : B α}
    (same : ∀ before, (action le before).2.blocks = before.blocks) : EmittedProfileRun profile le action := by
  intro before result after run checked inst member
  have blocks := same before
  rw [run] at blocks
  change after.blocks = before.blocks at blocks
  exact checked inst (by simpa only [LS.insts, blocks] using member)

theorem EmittedProfileRun.recordValueRootRecipe {profile : ArtifactProfile} {le : LEnv}
    (value : ValueId) (sourceScope : ScopeId) :
    EmittedProfileRun profile le (Goose.Lower.recordValueRootRecipe value sourceScope) := by
  apply EmittedProfileRun.of_blocks_eq
  intro before
  rw [recordValueRootRecipe_run]

theorem EmittedProfileRun.recordReadValueRootRecipe {profile : ArtifactProfile} {le : LEnv}
    (value : ValueId) (place : Place) :
    EmittedProfileRun profile le (Goose.Lower.recordReadValueRootRecipe value place) := by
  apply EmittedProfileRun.of_blocks_eq
  intro before
  cases place <;> simp only [recordReadValueRootRecipe_run]
  split <;> simp [recordValueRootSource_run]

theorem EmittedProfile.appendInst {profile : ArtifactProfile} {before : LS}
    (checked : EmittedProfile profile before) (block : BlockId) (inst : Inst)
    (allowed : EmittedProfileInst profile inst) : EmittedProfile profile (before.appendInst block inst) := by
  intro actual member
  rcases insts_appendInst_member member with old | rfl
  · exact checked actual old
  · exact allowed

theorem EmittedProfileRun.emitDef {profile : ArtifactProfile} {le : LEnv} (op : Op)
    (allowed : ∀ value, EmittedProfileInst profile (.def value op)) : EmittedProfileRun profile le (Goose.Lower.emitDef op) := by
  intro before result after run checked
  cases live : before.cur with
  | none => rw [emitDef_none op le live] at run; obtain ⟨_, rfl⟩ := Prod.mk.inj run; exact checked
  | some block =>
    rw [emitDef_run op le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked.appendInst block (.def before.vals.size op) (allowed _)

theorem EmittedProfileRun.emitEffect {profile : ArtifactProfile} {le : LEnv} (effect : Effect)
    (allowed : EmittedProfileInst profile (.eff effect)) : EmittedProfileRun profile le (Goose.Lower.emitEffect effect) := by
  intro before result after run checked
  cases live : before.cur with
  | none => rw [emitEffect_none effect le live] at run; obtain ⟨_, rfl⟩ := Prod.mk.inj run; exact checked
  | some block =>
    rw [emitEffect_run effect le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked.appendInst block (.eff effect) allowed

theorem EmittedProfileRun.emitTerm {profile : ArtifactProfile} {le : LEnv} (term : Term)
    (allowed : EmittedProfileInst profile (.term term)) : EmittedProfileRun profile le (Goose.Lower.emitTerm term) := by
  intro before result after run checked
  cases live : before.cur with
  | none => rw [emitTerm_none term le live] at run; obtain ⟨_, rfl⟩ := Prod.mk.inj run; exact checked
  | some block =>
    rw [emitTerm_run term le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked.appendInst block (.term term) allowed

theorem EmittedProfileRun.patchTerm {profile : ArtifactProfile} {le : LEnv} (block : BlockId) (term : Term)
    (allowed : EmittedProfileInst profile (.term term)) : EmittedProfileRun profile le (Goose.Lower.patchTerm block term) := by
  intro before result after run checked
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact checked.appendInst block (.term term) allowed

theorem EmittedProfileRun.newBlock {profile : ArtifactProfile} {le : LEnv} (types : List VTy) :
    EmittedProfileRun profile le (Goose.Lower.newBlock types) := by
  intro before result after run checked inst member
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact checked inst (by simpa [LS.insts] using member)

theorem EmittedProfileRun.setCur {profile : ArtifactProfile} {le : LEnv} (current : Option BlockId) :
    EmittedProfileRun profile le (Goose.Lower.setCur current) := .of_blocks_eq (fun _ => rfl)

theorem EmittedProfileRun.read {profile : ArtifactProfile} {le : LEnv} : EmittedProfileRun profile le (read : B LEnv) :=
  .of_blocks_eq (fun _ => rfl)

theorem EmittedProfileRun.get {profile : ArtifactProfile} {le : LEnv} : EmittedProfileRun profile le (get : B LS) :=
  .of_blocks_eq (fun _ => rfl)

theorem EmittedProfileRun.curBlock {profile : ArtifactProfile} {le : LEnv} : EmittedProfileRun profile le Goose.Lower.curBlock :=
  .of_blocks_eq (fun _ => rfl)

theorem EmittedProfileRun.isLive {profile : ArtifactProfile} {le : LEnv} : EmittedProfileRun profile le Goose.Lower.isLive :=
  .of_blocks_eq (fun _ => rfl)

theorem EmittedProfileRun.valTy {profile : ArtifactProfile} {le : LEnv} (value : ValueId) : EmittedProfileRun profile le (Goose.Lower.valTy value) :=
  .of_blocks_eq (fun before => by rw [valTy_run])

theorem EmittedProfileRun.intTyOf {profile : ArtifactProfile} {le : LEnv} (value : ValueId) : EmittedProfileRun profile le (Goose.Lower.intTyOf value) :=
  .of_blocks_eq (fun before => congrArg LS.blocks (intTyOf_state value le before))

theorem EmittedProfileRun.pushScope {profile : ArtifactProfile} {le : LEnv} (scope : ScopeId) :
    EmittedProfileRun profile le (Goose.Lower.pushScope scope) := .of_blocks_eq (fun _ => rfl)

theorem EmittedProfileRun.popScope {profile : ArtifactProfile} {le : LEnv} : EmittedProfileRun profile le Goose.Lower.popScope :=
  .of_blocks_eq (fun _ => rfl)

end Goose.Lower.Validation
