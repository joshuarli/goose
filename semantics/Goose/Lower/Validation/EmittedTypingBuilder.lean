import Goose.Lower.Validation.EmittedTypingTrace

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def EmittedAt (le : LEnv) (before : LS) (action : B α) : Prop :=
  EmittedTrace le before (action le before).2

theorem EmittedAt.pure (le : LEnv) (before : LS) (value : α) : EmittedAt le before (Pure.pure value) := .refl

theorem EmittedAt.bind {le : LEnv} {before : LS} {first : B α} {next : α → B β}
    (firstTrace : EmittedAt le before first)
    (nextTrace : EmittedAt le (first le before).2 (next (first le before).1)) :
    EmittedAt le before (first >>= next) := firstTrace.append nextTrace

theorem EmittedAt.of_preserving {le : LEnv} {before : LS} (action : B α)
    (retained : EmittedTypePrefix before (action le before).2)
    (definitions : ∀ value op, .def value op ∈ (action le before).2.insts → .def value op ∈ before.insts) :
    EmittedAt le before action := .preserve action (action le before).1 .refl rfl retained definitions

theorem EmittedAt.of_state {le : LEnv} {before : LS} (action : B α)
    (unchanged : (action le before).2 = before) : EmittedAt le before action := by
  unfold EmittedAt
  rw [unchanged]
  exact .refl

theorem EmittedAt.emitDef {le : LEnv} {before : LS} (op : Op)
    (success : before.cur.isSome = true → ∃ type, op.resultTy (tyEnv le before) = .ok type) :
    EmittedAt le before (Goose.Lower.emitDef op) := by
  cases live : before.cur with
  | none => apply EmittedAt.of_state; exact congrArg Prod.snd (emitDef_none _ _ live)
  | some block => obtain ⟨type, typed⟩ := success (by simp [live]); exact .emit .refl op type typed

theorem EmittedAt.emitEffect (le : LEnv) (before : LS) (effect : Effect) :
    EmittedAt le before (Goose.Lower.emitEffect effect) := by
  cases live : before.cur with
  | none => apply EmittedAt.of_state; exact congrArg Prod.snd (emitEffect_none _ _ live)
  | some block =>
    apply EmittedAt.of_preserving
    · rw [emitEffect_run _ _ live]
      exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
    · intro value op member
      rw [emitEffect_run _ _ live] at member
      rcases emittedDef_appendInst member with previous | fresh
      · exact previous
      · cases fresh

theorem EmittedAt.emitTerm (le : LEnv) (before : LS) (term : Term) :
    EmittedAt le before (Goose.Lower.emitTerm term) := by
  cases live : before.cur with
  | none => apply EmittedAt.of_state; exact congrArg Prod.snd (emitTerm_none _ _ live)
  | some block =>
    apply EmittedAt.of_preserving
    · rw [emitTerm_run _ _ live]
      exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
    · intro value op member
      rw [emitTerm_run _ _ live] at member
      have same : .def value op ∈ (before.appendInst block (.term term)).insts := member
      rcases emittedDef_appendInst same with previous | fresh
      · exact previous
      · cases fresh

theorem EmittedAt.patchTerm (le : LEnv) (before : LS) (block : BlockId) (term : Term) :
    EmittedAt le before (Goose.Lower.patchTerm block term) := by
  apply EmittedAt.of_preserving
  · rw [patchTerm_run]
    exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  · intro value op member
    rw [patchTerm_run] at member
    rcases emittedDef_appendInst member with previous | fresh
    · exact previous
    · cases fresh

theorem EmittedAt.newBlock (le : LEnv) (before : LS) (types : List VTy) :
    EmittedAt le before (Goose.Lower.newBlock types) := by
  apply EmittedAt.of_preserving _ (emittedTypePrefix_newBlock types le before)
  intro value op member
  rw [newBlock_run_general] at member
  simpa only [LS.insts, Array.toList_push, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, Array.toList_empty, List.nil_append, List.append_nil] using member

theorem EmittedAt.setCur (le : LEnv) (before : LS) (block : Option BlockId) :
    EmittedAt le before (Goose.Lower.setCur block) := by
  apply EmittedAt.of_preserving
  · rw [setCur_run]
    exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  · intro value op member
    rw [setCur_run] at member
    exact member

theorem EmittedAt.pushScope (le : LEnv) (before : LS) (scope : ScopeId) :
    EmittedAt le before (Goose.Lower.pushScope scope) := by
  apply EmittedAt.of_preserving
  · exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  · exact fun _ _ member => member

theorem EmittedAt.popScope (le : LEnv) (before : LS) :
    EmittedAt le before Goose.Lower.popScope := by
  apply EmittedAt.of_preserving
  · exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  · exact fun _ _ member => member

theorem EmittedAt.get (le : LEnv) (before : LS) : EmittedAt le before (get : B LS) := .refl

theorem EmittedAt.read (le : LEnv) (before : LS) : EmittedAt le before (read : B LEnv) := .refl

theorem EmittedAt.curBlock (le : LEnv) (before : LS) : EmittedAt le before Goose.Lower.curBlock := .refl

theorem EmittedAt.isLive (le : LEnv) (before : LS) : EmittedAt le before Goose.Lower.isLive := .refl

theorem EmittedAt.valTy (le : LEnv) (before : LS) (value : ValueId) :
    EmittedAt le before (Goose.Lower.valTy value) := by
  apply EmittedAt.of_state
  cases row : before.vals[value]? with
  | none => simp [Goose.Lower.valTy, bind_run, row, pure_run]
  | some ty => cases ty <;> simp [Goose.Lower.valTy, bind_run, row, pure_run]

theorem EmittedAt.intTyOf (le : LEnv) (before : LS) (value : ValueId) :
    EmittedAt le before (Goose.Lower.intTyOf value) := by
  apply EmittedAt.of_state
  cases row : before.vals[value]? with
  | none => simp [Goose.Lower.intTyOf, Goose.Lower.valTy, bind_run, row, pure_run]
  | some ty => cases ty with
    | none => simp [Goose.Lower.intTyOf, Goose.Lower.valTy, bind_run, row, pure_run]
    | some type => cases type with
      | view _ _ => simp [Goose.Lower.intTyOf, Goose.Lower.valTy, bind_run, row, pure_run]
      | data type => cases type <;> simp [Goose.Lower.intTyOf, Goose.Lower.valTy, bind_run, row, pure_run]

end Goose.Lower.Validation
