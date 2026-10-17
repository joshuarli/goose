import Goose.Lower.Validation.EmittedMetadataChecking
import Goose.Lower.Validation.OperandBounds

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def EmittedMetadataInst (le : LEnv) (state : LS) : Inst → Prop
  | .def .. => True
  | .eff effect => EmittedEffectTyped le state effect
  | .term term => EmittedTermTyped le.results state term

def EmittedMetadata (le : LEnv) (state : LS) : Prop :=
  ∀ inst ∈ state.insts, EmittedMetadataInst le state inst

theorem EmittedMetadataInst.retained {le : LEnv} {before after : LS} {inst : Inst}
    (typed : EmittedMetadataInst le before inst) (preserved : TypePrefix before after) :
    EmittedMetadataInst le after inst := by
  cases inst with
  | «def» _ _ => trivial
  | eff _ => exact EmittedEffectTyped.retained typed preserved
  | term _ => exact EmittedTermTyped.retained typed preserved

theorem EmittedMetadata.of_preserving {le : LEnv} {before after : LS}
    (typed : EmittedMetadata le before) (preserved : TypePrefix before after)
    (instructions : ∀ inst ∈ after.insts, inst ∈ before.insts ∨ EmittedMetadataInst le before inst) :
    EmittedMetadata le after := by
  intro inst member
  rcases instructions inst member with prior | added
  · exact (typed inst prior).retained preserved
  · exact added.retained preserved

theorem EmittedMetadata.initState (le : LEnv) : EmittedMetadata le initState := by
  intro inst member
  cases member

theorem EmittedMetadata.emitDef {le : LEnv} {before : LS} (typed : EmittedMetadata le before) (op : Op) :
    EmittedMetadata le (Goose.Lower.emitDef op le before).2 := by
  refine typed.of_preserving (after := (Goose.Lower.emitDef op le before).2) (types_emitDef op le before _ _ rfl) ?_
  intro inst member
  cases live : before.cur with
  | none => exact Or.inl (by simpa only [emitDef_none op le live] using member)
  | some block =>
    rw [emitDef_run op le live] at member
    rcases insts_appendInst_member (before := { before with vals := before.vals.push (some ((op.resultTy (tyEnv le before)).toOption.getD (.data .unit))) }) member with old | rfl
    · exact Or.inl old
    · exact Or.inr trivial

theorem EmittedMetadata.emitEffect {le : LEnv} {before : LS} (typed : EmittedMetadata le before) (effect : Effect)
    (effectTyped : before.cur.isSome = true → EmittedEffectTyped le before effect) :
    EmittedMetadata le (Goose.Lower.emitEffect effect le before).2 := by
  refine typed.of_preserving (after := (Goose.Lower.emitEffect effect le before).2) (types_emitEffect effect le before _ _ rfl) ?_
  intro inst member
  cases live : before.cur with
  | none => exact Or.inl (by simpa only [emitEffect_none effect le live] using member)
  | some block =>
    rw [emitEffect_run effect le live] at member
    rcases insts_appendInst_member member with old | rfl
    · exact Or.inl old
    · exact Or.inr (effectTyped (by simp [live]))

theorem EmittedMetadata.emitTerm {le : LEnv} {before : LS} (typed : EmittedMetadata le before) (term : Term)
    (termTyped : before.cur.isSome = true → EmittedTermTyped le.results before term) :
    EmittedMetadata le (Goose.Lower.emitTerm term le before).2 := by
  refine typed.of_preserving (after := (Goose.Lower.emitTerm term le before).2) (types_emitTerm term le before _ _ rfl) ?_
  intro inst member
  cases live : before.cur with
  | none => exact Or.inl (by simpa only [emitTerm_none term le live] using member)
  | some block =>
    rw [emitTerm_run term le live] at member
    rcases insts_appendInst_member member with old | rfl
    · exact Or.inl old
    · exact Or.inr (termTyped (by simp [live]))

theorem EmittedMetadata.patchTerm {le : LEnv} {before : LS} (typed : EmittedMetadata le before)
    (block : BlockId) (term : Term) (termTyped : EmittedTermTyped le.results before term) :
    EmittedMetadata le (Goose.Lower.patchTerm block term le before).2 := by
  refine typed.of_preserving (after := (Goose.Lower.patchTerm block term le before).2) (types_patchTerm block term le before _ _ rfl) ?_
  intro inst member
  rw [patchTerm_run] at member
  rcases insts_appendInst_member member with old | rfl
  · exact Or.inl old
  · exact Or.inr termTyped

theorem EmittedMetadata.newBlock {le : LEnv} {before : LS} (typed : EmittedMetadata le before)
    (types : List VTy) : EmittedMetadata le (Goose.Lower.newBlock types le before).2 := by
  refine typed.of_preserving (after := (Goose.Lower.newBlock types le before).2) (types_newBlock types le before _ _ rfl) ?_
  intro inst member
  exact Or.inl (by simpa [newBlock_run_general, LS.insts] using member)

theorem EmittedMetadata.setCur {le : LEnv} {before : LS} (typed : EmittedMetadata le before)
    (current : Option BlockId) : EmittedMetadata le (Goose.Lower.setCur current le before).2 := by
  refine typed.of_preserving (types_setCur current le before _ _ rfl) ?_
  intro inst member
  exact Or.inl member

theorem EmittedMetadata.pushScope {le : LEnv} {before : LS} (typed : EmittedMetadata le before)
    (scope : ScopeId) : EmittedMetadata le (Goose.Lower.pushScope scope le before).2 := by
  refine typed.of_preserving (types_pushScope scope le before _ _ rfl) ?_
  intro inst member
  exact Or.inl member

theorem EmittedMetadata.popScope {le : LEnv} {before : LS} (typed : EmittedMetadata le before) :
    EmittedMetadata le (Goose.Lower.popScope le before).2 := by
  refine typed.of_preserving (types_popScope le before _ _ rfl) ?_
  intro inst member
  exact Or.inl member

end Goose.Lower.Validation
