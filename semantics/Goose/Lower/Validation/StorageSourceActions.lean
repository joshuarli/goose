import Goose.Lower.Validation.StorageSourceBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def StorageAt (le : LEnv) (before : LS) (action : B α) : Prop :=
  StorageBuilder le.mod.profile before → StorageBuilder le.mod.profile (action le before).2

theorem StorageAt.bind {le : LEnv} {before : LS} {first : B α} {next : α → B β}
    (firstStorage : StorageAt le before first)
    (nextStorage : StorageAt le (first le before).2 (next (first le before).1)) :
    StorageAt le before (first >>= next) := fun checked => nextStorage (firstStorage checked)

theorem StorageAt.pure (le : LEnv) (before : LS) (value : α) : StorageAt le before (pure value) :=
  fun checked => checked

theorem StorageAt.of_state {le : LEnv} {before : LS} {action : B α}
    (same : (action le before).2 = before) : StorageAt le before action := by
  intro checked
  rw [same]
  exact checked

theorem StorageAt.of_preserving {le : LEnv} {before : LS} {action : B α}
    (types : TypePrefix before (action le before).2)
    (instructions : ∀ instruction ∈ (action le before).2.insts, instruction ∈ before.insts) :
    StorageAt le before action := fun checked => checked.retained types instructions

theorem StorageAt.emitDef {le : LEnv} {before : LS} (op : Op)
    (emitted : before.cur.isSome = true → ∀ value, StorageAuthority le.mod.profile before.vals (.def value op)) :
    StorageAt le before (Goose.Lower.emitDef op) := by
  intro checked
  cases live : before.cur with
  | none => rw [emitDef_none op le live]; exact checked
  | some block => exact checked.emitDef (emitted (by simp [live])) rfl

theorem StorageAt.emitEffect {le : LEnv} {before : LS} (effect : Effect)
    (emitted : before.cur.isSome = true → StorageAuthority le.mod.profile before.vals (.eff effect)) :
    StorageAt le before (Goose.Lower.emitEffect effect) := by
  intro checked
  cases live : before.cur with
  | none => rw [emitEffect_none effect le live]; exact checked
  | some block => exact checked.emitEffect (emitted (by simp [live])) rfl

theorem StorageAt.emitTerm (le : LEnv) (before : LS) (term : Term) :
    StorageAt le before (Goose.Lower.emitTerm term) := fun checked => checked.emitTerm rfl

theorem StorageAt.patchTerm (le : LEnv) (before : LS) (block : BlockId) (term : Term) :
    StorageAt le before (Goose.Lower.patchTerm block term) := fun checked => checked.patchTerm rfl

theorem StorageAt.newBlock (le : LEnv) (before : LS) (types : List VTy) :
    StorageAt le before (Goose.Lower.newBlock types) := fun checked => checked.newBlock rfl

theorem StorageAt.setCur (le : LEnv) (before : LS) (current : Option BlockId) :
    StorageAt le before (Goose.Lower.setCur current) := fun checked => checked

theorem StorageAt.get (le : LEnv) (before : LS) : StorageAt le before (get : B LS) :=
  fun checked => checked

theorem StorageAt.read (le : LEnv) (before : LS) : StorageAt le before (read : B LEnv) :=
  fun checked => checked

theorem StorageAt.curBlock (le : LEnv) (before : LS) : StorageAt le before Goose.Lower.curBlock :=
  fun checked => checked

theorem StorageAt.valTy (le : LEnv) (before : LS) (value : ValueId) :
    StorageAt le before (Goose.Lower.valTy value) := by
  apply StorageAt.of_state
  rw [valTy_run]

theorem StorageAt.intTyOf (le : LEnv) (before : LS) (value : ValueId) :
    StorageAt le before (Goose.Lower.intTyOf value) := by
  unfold Goose.Lower.intTyOf
  apply (StorageAt.valTy _ _ _).bind
  cases (Goose.Lower.valTy value le before).1 with
  | data ty => cases ty <;> exact StorageAt.pure _ _ _
  | view _ _ => exact StorageAt.pure _ _ _

theorem StorageAt.whenLive {le : LEnv} {before : LS} (default : α) (action : BlockId → B α)
    (branches : ∀ block, before.cur = some block → StorageAt le before (action block)) :
    StorageAt le before (Goose.Lower.whenLive default action) := by
  cases live : before.cur with
  | none => apply StorageAt.of_state; exact congrArg Prod.snd (whenLive_none _ _ _ live)
  | some block => simpa only [StorageAt, whenLive_some _ _ _ live] using branches block live

end Goose.Lower.Validation
