import Goose.Lower.Validation.ReplacementSourceSitesBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

variable {root : DemandNode} {targets : List BlockId}

def ReplacementSitesFree (le : LEnv) (before : LS) (action : B α) : Prop :=
  ReplacementSitesBuilder (root := root) (targets := targets) le before →
    before.Ext (action le before).2 ∧ ReplacementSitesBuilder (root := root) (targets := targets) le (action le before).2

def ReplacementSitesAt (le : LEnv) (before : LS) (action : B α) : Prop :=
  ReplacementTargetsBound targets before → ReplacementSitesFree (root := root) (targets := targets) le before action

theorem ReplacementSitesFree.bind {le : LEnv} {before : LS} {first : B α} {next : α → B β}
    (one : ReplacementSitesFree (root := root) (targets := targets) le before first)
    (two : ReplacementSitesFree (root := root) (targets := targets) le (first le before).2 (next (first le before).1)) :
    ReplacementSitesFree (root := root) (targets := targets) le before (first >>= next) := by
  intro checked
  obtain ⟨firstExt, middle⟩ := one checked
  obtain ⟨nextExt, finalState⟩ := two middle
  exact ⟨firstExt.trans nextExt, finalState⟩

theorem ReplacementSitesFree.at {le : LEnv} {before : LS} {action : B α}
    (free : ReplacementSitesFree (root := root) (targets := targets) le before action) :
    ReplacementSitesAt (root := root) (targets := targets) le before action := fun _ => free

theorem ReplacementSitesAt.bind {le : LEnv} {before : LS} {first : B α} {next : α → B β}
    (one : ReplacementSitesAt (root := root) (targets := targets) le before first)
    (two : ReplacementSitesAt (root := root) (targets := targets) le (first le before).2 (next (first le before).1)) :
    ReplacementSitesAt (root := root) (targets := targets) le before (first >>= next) := by
  intro bounded checked
  obtain ⟨firstExt, middle⟩ := one bounded checked
  obtain ⟨nextExt, finalState⟩ := two (bounded.mono firstExt) middle
  exact ⟨firstExt.trans nextExt, finalState⟩

theorem ReplacementSitesAt.reserve_prefix {le : LEnv} {before : LS} {first : B α} {next : α → B β}
    (extra : List BlockId) (fresh : ∀ target ∈ extra, before.blocks.size ≤ target)
    (one : ReplacementSitesFree (root := root) (targets := extra ++ targets) le before first)
    (boundedExtra : ∀ target ∈ extra, target < (first le before).2.blocks.size)
    (two : ReplacementSitesAt (root := root) (targets := extra ++ targets) le (first le before).2 (next (first le before).1)) :
    ReplacementSitesAt (root := root) (targets := targets) le before (first >>= next) := by
  intro bounded checked
  obtain ⟨firstExt, middle⟩ := one (checked.reserveMany extra fresh)
  have extendedBound : ReplacementTargetsBound (extra ++ targets) (first le before).2 := by
    intro target member
    rcases List.mem_append.mp member with added | inherited
    · exact boundedExtra target added
    · exact (bounded.mono firstExt) target inherited
  obtain ⟨nextExt, finalState⟩ := two extendedBound middle
  exact ⟨firstExt.trans nextExt, finalState.weaken (fun target member => List.mem_append_right extra member)⟩

theorem ReplacementSitesFree.pure (le : LEnv) (before : LS) (value : α) :
    ReplacementSitesFree (root := root) (targets := targets) le before (pure value) := fun checked => ⟨.refl _, checked⟩

theorem ReplacementSitesAt.pure (le : LEnv) (before : LS) (value : α) :
    ReplacementSitesAt (root := root) (targets := targets) le before (pure value) := (ReplacementSitesFree.pure le before value).at

theorem ReplacementSitesAt.of_state {le : LEnv} {before : LS} {action : B α}
    (same : (action le before).2 = before) : ReplacementSitesAt (root := root) (targets := targets) le before action := by
  intro _ checked
  rw [same]
  exact ⟨.refl _, checked⟩

theorem ReplacementSitesAt.recordValueRootSource (le : LEnv) (before : LS) (value : ValueId)
    (source : ValueRootSource) :
    ReplacementSitesAt (root := root) (targets := targets) le before
      (Goose.Lower.recordValueRootSource value source) := by
  intro _ checked
  rw [recordValueRootSource_run]
  exact ⟨.refl _, checked.of_emits (.of_blocks rfl) (.refl _) (.of_blocks rfl)⟩

theorem ReplacementSitesAt.recordReadValueRootRecipe (le : LEnv) (before : LS) (value : ValueId)
    (place : Place) :
    ReplacementSitesAt (root := root) (targets := targets) le before
      (Goose.Lower.recordReadValueRootRecipe value place) := by
  intro bounded checked
  cases place <;> simp only [recordReadValueRootRecipe_run]
  all_goals try exact ⟨.refl _, checked⟩
  split
  · exact ReplacementSitesAt.recordValueRootSource le before value _ bounded checked
  · exact ⟨.refl _, checked⟩

theorem ReplacementSitesFree.emitDef {le : LEnv} {before : LS} (op : Op)
    (emitted : before.cur.isSome = true → ∀ value, NotReplacement (.def value op)) :
    ReplacementSitesFree (root := root) (targets := targets) le before (Goose.Lower.emitDef op) := by
  intro checked
  refine ⟨(advB_emitDef op le before _ _ rfl).ext, ?_⟩
  cases live : before.cur with
  | none => rw [emitDef_none op le live]; exact checked
  | some block => exact checked.emitDef (emitted (by simp [live])) rfl

theorem ReplacementSitesAt.emitDef {le : LEnv} {before : LS} (op : Op)
    (emitted : before.cur.isSome = true → ∀ value, NotReplacement (.def value op)) :
    ReplacementSitesAt (root := root) (targets := targets) le before (Goose.Lower.emitDef op) :=
  (ReplacementSitesFree.emitDef op emitted).at

theorem ReplacementSitesFree.emitEffect {le : LEnv} {before : LS} (effect : Effect)
    (emitted : before.cur.isSome = true → NotReplacement (.eff effect)) :
    ReplacementSitesFree (root := root) (targets := targets) le before (Goose.Lower.emitEffect effect) := by
  intro checked
  refine ⟨(advB_emitEffect effect le before _ _ rfl).ext, ?_⟩
  cases live : before.cur with
  | none => rw [emitEffect_none effect le live]; exact checked
  | some block => exact checked.emitEffect (emitted (by simp [live])) rfl

theorem ReplacementSitesAt.emitEffect {le : LEnv} {before : LS} (effect : Effect)
    (emitted : before.cur.isSome = true → NotReplacement (.eff effect)) :
    ReplacementSitesAt (root := root) (targets := targets) le before (Goose.Lower.emitEffect effect) :=
  (ReplacementSitesFree.emitEffect effect emitted).at

theorem ReplacementSitesFree.emitTerm (le : LEnv) (before : LS) (term : Term)
    (allowed : ∀ target ∈ term.successors, target ∈ targets ∨ before.blocks.size ≤ target) :
    ReplacementSitesFree (root := root) (targets := targets) le before (Goose.Lower.emitTerm term) :=
  fun checked => ⟨(advB_emitTerm term le before _ _ rfl).ext, checked.emitTerm allowed rfl⟩

theorem ReplacementSitesAt.emitTerm (le : LEnv) (before : LS) (term : Term)
    (allowed : ∀ target ∈ term.successors, target ∈ targets ∨ before.blocks.size ≤ target := by
      simp [Term.successors]) :
    ReplacementSitesAt (root := root) (targets := targets) le before (Goose.Lower.emitTerm term) :=
  (ReplacementSitesFree.emitTerm le before term allowed).at

theorem ReplacementSitesFree.patchTerm (le : LEnv) (before : LS) (block : BlockId) (term : Term)
    (allowed : ∀ target ∈ term.successors, target ∈ targets ∨ before.blocks.size ≤ target) :
    ReplacementSitesFree (root := root) (targets := targets) le before (Goose.Lower.patchTerm block term) :=
  fun checked => ⟨patchTerm_ext (env := le) rfl, checked.patchTerm rfl allowed⟩

theorem ReplacementSitesAt.patchTerm (le : LEnv) (before : LS) (block : BlockId) (term : Term)
    (allowed : ∀ target ∈ term.successors, target ∈ targets ∨ before.blocks.size ≤ target := by
      simp [Term.successors]) :
    ReplacementSitesAt (root := root) (targets := targets) le before (Goose.Lower.patchTerm block term) :=
  (ReplacementSitesFree.patchTerm le before block term allowed).at

theorem ReplacementSitesFree.newBlock (le : LEnv) (before : LS) (types : List VTy) :
    ReplacementSitesFree (root := root) (targets := targets) le before (Goose.Lower.newBlock types) := by
  intro checked
  have framed := generatedTargetFrame_newBlock none types before le before _ _ (.refl _) trivial
    (TermEdgesFramed.refl none before) rfl
  exact ⟨framed.2, checked.newBlock rfl⟩

theorem ReplacementSitesAt.newBlock (le : LEnv) (before : LS) (types : List VTy) :
    ReplacementSitesAt (root := root) (targets := targets) le before (Goose.Lower.newBlock types) :=
  (ReplacementSitesFree.newBlock le before types).at

theorem ReplacementSitesFree.setCur (le : LEnv) (before : LS) (current : Option BlockId) :
    ReplacementSitesFree (root := root) (targets := targets) le before (Goose.Lower.setCur current) :=
  fun checked => ⟨.refl _, checked.of_emits (.of_blocks rfl) (.refl _) (.of_blocks rfl)⟩

theorem ReplacementSitesAt.setCur (le : LEnv) (before : LS) (current : Option BlockId) :
    ReplacementSitesAt (root := root) (targets := targets) le before (Goose.Lower.setCur current) :=
  (ReplacementSitesFree.setCur le before current).at

theorem ReplacementSitesAt.get (le : LEnv) (before : LS) : ReplacementSitesAt (root := root) (targets := targets) le before (get : B LS) :=
  fun _ checked => ⟨.refl _, checked⟩

theorem ReplacementSitesAt.read (le : LEnv) (before : LS) : ReplacementSitesAt (root := root) (targets := targets) le before (read : B LEnv) :=
  fun _ checked => ⟨.refl _, checked⟩

theorem ReplacementSitesAt.curBlock (le : LEnv) (before : LS) : ReplacementSitesAt (root := root) (targets := targets) le before Goose.Lower.curBlock :=
  fun _ checked => ⟨.refl _, checked⟩

theorem ReplacementSitesAt.valTy (le : LEnv) (before : LS) (value : ValueId) :
    ReplacementSitesAt (root := root) (targets := targets) le before (Goose.Lower.valTy value) := by
  apply ReplacementSitesAt.of_state
  rw [valTy_run]

theorem ReplacementSitesAt.intTyOf (le : LEnv) (before : LS) (value : ValueId) :
    ReplacementSitesAt (root := root) (targets := targets) le before (Goose.Lower.intTyOf value) := by
  unfold Goose.Lower.intTyOf
  apply (ReplacementSitesAt.valTy _ _ _).bind
  cases (Goose.Lower.valTy value le before).1 with
  | data ty => cases ty <;> exact ReplacementSitesAt.pure _ _ _
  | view _ _ => exact ReplacementSitesAt.pure _ _ _

theorem ReplacementSitesAt.whenLive {le : LEnv} {before : LS} (default : α) (action : BlockId → B α)
    (branches : ∀ block, before.cur = some block → ReplacementSitesAt (root := root) (targets := targets) le before (action block)) :
    ReplacementSitesAt (root := root) (targets := targets) le before (Goose.Lower.whenLive default action) := by
  cases live : before.cur with
  | none => apply ReplacementSitesAt.of_state; exact congrArg Prod.snd (whenLive_none _ _ _ live)
  | some block => simpa only [ReplacementSitesAt, ReplacementSitesFree, whenLive_some _ _ _ live] using branches block live

end Goose.Lower.Validation
