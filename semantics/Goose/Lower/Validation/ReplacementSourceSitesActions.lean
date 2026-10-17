import Goose.Lower.Validation.ReplacementSourceSitesBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def ReplacementSitesAt (le : LEnv) (before : LS) (action : B α) : Prop :=
  ReplacementSitesBuilder le before → ReplacementSitesBuilder le (action le before).2

theorem ReplacementSitesAt.bind {le : LEnv} {before : LS} {first : B α} {next : α → B β}
    (firstStorage : ReplacementSitesAt le before first)
    (nextStorage : ReplacementSitesAt le (first le before).2 (next (first le before).1)) :
    ReplacementSitesAt le before (first >>= next) := fun checked => nextStorage (firstStorage checked)

theorem ReplacementSitesAt.pure (le : LEnv) (before : LS) (value : α) : ReplacementSitesAt le before (pure value) :=
  fun checked => checked

theorem ReplacementSitesAt.of_state {le : LEnv} {before : LS} {action : B α}
    (same : (action le before).2 = before) : ReplacementSitesAt le before action := by
  intro checked
  rw [same]
  exact checked

theorem ReplacementSitesAt.emitDef {le : LEnv} {before : LS} (op : Op)
    (emitted : before.cur.isSome = true → ∀ value, NotReplacement (.def value op)) :
    ReplacementSitesAt le before (Goose.Lower.emitDef op) := by
  intro checked
  cases live : before.cur with
  | none => rw [emitDef_none op le live]; exact checked
  | some block => exact checked.emitDef (emitted (by simp [live])) rfl

theorem ReplacementSitesAt.emitEffect {le : LEnv} {before : LS} (effect : Effect)
    (emitted : before.cur.isSome = true → NotReplacement (.eff effect)) :
    ReplacementSitesAt le before (Goose.Lower.emitEffect effect) := by
  intro checked
  cases live : before.cur with
  | none => rw [emitEffect_none effect le live]; exact checked
  | some block => exact checked.emitEffect (emitted (by simp [live])) rfl

theorem ReplacementSitesAt.emitTerm (le : LEnv) (before : LS) (term : Term) :
    ReplacementSitesAt le before (Goose.Lower.emitTerm term) := fun checked => checked.emitTerm rfl

theorem ReplacementSitesAt.patchTerm (le : LEnv) (before : LS) (block : BlockId) (term : Term) :
    ReplacementSitesAt le before (Goose.Lower.patchTerm block term) := fun checked => checked.patchTerm rfl

theorem ReplacementSitesAt.newBlock (le : LEnv) (before : LS) (types : List VTy) :
    ReplacementSitesAt le before (Goose.Lower.newBlock types) := fun checked => checked.newBlock rfl

theorem ReplacementSitesAt.setCur (le : LEnv) (before : LS) (current : Option BlockId) :
    ReplacementSitesAt le before (Goose.Lower.setCur current) := fun checked => checked.of_emits (.of_blocks rfl) (.refl _)

theorem ReplacementSitesAt.get (le : LEnv) (before : LS) : ReplacementSitesAt le before (get : B LS) :=
  fun checked => checked

theorem ReplacementSitesAt.read (le : LEnv) (before : LS) : ReplacementSitesAt le before (read : B LEnv) :=
  fun checked => checked

theorem ReplacementSitesAt.curBlock (le : LEnv) (before : LS) : ReplacementSitesAt le before Goose.Lower.curBlock :=
  fun checked => checked

theorem ReplacementSitesAt.valTy (le : LEnv) (before : LS) (value : ValueId) :
    ReplacementSitesAt le before (Goose.Lower.valTy value) := by
  apply ReplacementSitesAt.of_state
  rw [valTy_run]

theorem ReplacementSitesAt.intTyOf (le : LEnv) (before : LS) (value : ValueId) :
    ReplacementSitesAt le before (Goose.Lower.intTyOf value) := by
  unfold Goose.Lower.intTyOf
  apply (ReplacementSitesAt.valTy _ _ _).bind
  cases (Goose.Lower.valTy value le before).1 with
  | data ty => cases ty <;> exact ReplacementSitesAt.pure _ _ _
  | view _ _ => exact ReplacementSitesAt.pure _ _ _

theorem ReplacementSitesAt.whenLive {le : LEnv} {before : LS} (default : α) (action : BlockId → B α)
    (branches : ∀ block, before.cur = some block → ReplacementSitesAt le before (action block)) :
    ReplacementSitesAt le before (Goose.Lower.whenLive default action) := by
  cases live : before.cur with
  | none => apply ReplacementSitesAt.of_state; exact congrArg Prod.snd (whenLive_none _ _ _ live)
  | some block => simpa only [ReplacementSitesAt, whenLive_some _ _ _ live] using branches block live

end Goose.Lower.Validation
