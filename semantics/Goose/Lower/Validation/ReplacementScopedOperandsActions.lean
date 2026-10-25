import Goose.Lower.Validation.ReplacementScopedFreshValues
import Goose.Lower.Validation.ReplacementEmission
import Goose.Lower.Validation.CfgReadRecipes

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def RhsUsesFresh (floor : Nat) (instruction : Inst) : Prop :=
  ∀ value ∈ instruction.uses, floor ≤ value

def RhsOperandsAt (floor : Nat) (env : LEnv) (before : LS) (action : B α) : Prop :=
  EmitsOnly (RhsUsesFresh floor) before (action env before).2

theorem RhsOperandsAt.bind {floor : Nat} {env : LEnv} {before : LS}
    {first : B α} {next : α → B β}
    (one : RhsOperandsAt floor env before first)
    (two : RhsOperandsAt floor env (first env before).2 (next (first env before).1)) :
    RhsOperandsAt floor env before (first >>= next) := one.trans two

theorem RhsOperandsAt.of_blocks {floor : Nat} {env : LEnv} {before : LS} {action : B α}
    (same : (action env before).2.blocks = before.blocks) : RhsOperandsAt floor env before action :=
  EmitsOnly.of_blocks same

theorem RhsOperandsAt.pure (floor : Nat) (env : LEnv) (before : LS) (value : α) :
    RhsOperandsAt floor env before (pure value) := .refl _ _

theorem RhsOperandsAt.emitDef (floor : Nat) (env : LEnv) (before : LS) (op : Op)
    (operands : before.cur.isSome = true → ∀ value ∈ op.uses, floor ≤ value) :
    RhsOperandsAt floor env before (emitDef op) := by
  cases current : before.cur with
  | none => apply RhsOperandsAt.of_blocks; rw [emitDef_none _ _ current]
  | some block =>
    exact emitsOnly_emitDef rfl (by simpa only [RhsUsesFresh, Inst.uses] using operands (by simp [current]))

theorem RhsOperandsAt.emitEffect (floor : Nat) (env : LEnv) (before : LS) (effect : Effect)
    (operands : before.cur.isSome = true → ∀ value ∈ effect.uses, floor ≤ value) :
    RhsOperandsAt floor env before (emitEffect effect) := by
  cases current : before.cur with
  | none => apply RhsOperandsAt.of_blocks; rw [emitEffect_none _ _ current]
  | some block =>
    exact emitsOnly_emitEffect effect (by simpa only [RhsUsesFresh, Inst.uses] using operands (by simp [current]))
      env before _ _ rfl

theorem RhsOperandsAt.emitTerm (floor : Nat) (env : LEnv) (before : LS) (term : Term)
    (operands : before.cur.isSome = true → ∀ value ∈ term.uses, floor ≤ value) :
    RhsOperandsAt floor env before (emitTerm term) := by
  cases current : before.cur with
  | none => apply RhsOperandsAt.of_blocks; rw [emitTerm_none _ _ current]
  | some block =>
    exact emitsOnly_emitTerm term (by simpa only [RhsUsesFresh, Inst.uses] using operands (by simp [current]))
      env before _ _ rfl

theorem RhsOperandsAt.patchTerm (floor : Nat) (env : LEnv) (before : LS) (block : BlockId) (term : Term)
    (operands : ∀ value ∈ term.uses, floor ≤ value) :
    RhsOperandsAt floor env before (patchTerm block term) := by
  unfold RhsOperandsAt
  rw [patchTerm_run]
  exact EmitsOnly.append before block (.term term) operands

theorem RhsOperandsAt.newBlock (floor : Nat) (env : LEnv) (before : LS) (types : List VTy) :
    RhsOperandsAt floor env before (newBlock types) := by
  unfold RhsOperandsAt
  rw [newBlock_run_general]
  exact (EmitsOnly.newBlock before _).trans (.of_blocks rfl)

theorem RhsOperandsAt.setCur (floor : Nat) (env : LEnv) (before : LS) (current : Option BlockId) :
    RhsOperandsAt floor env before (setCur current) := .of_blocks rfl

theorem RhsOperandsAt.read (floor : Nat) (env : LEnv) (before : LS) :
    RhsOperandsAt floor env before (read : B LEnv) := .of_blocks rfl

theorem RhsOperandsAt.get (floor : Nat) (env : LEnv) (before : LS) :
    RhsOperandsAt floor env before (get : B LS) := .of_blocks rfl

theorem RhsOperandsAt.valTy (floor : Nat) (env : LEnv) (before : LS) (value : ValueId) :
    RhsOperandsAt floor env before (valTy value) := .of_blocks (congrArg LS.blocks (valTy_run value env before))

theorem RhsOperandsAt.intTyOf (floor : Nat) (env : LEnv) (before : LS) (value : ValueId) :
    RhsOperandsAt floor env before (intTyOf value) :=
  .of_blocks (congrArg LS.blocks (intTyOf_eq (v := value) (le := env) (ls := before) rfl))

theorem RhsOperandsAt.curBlock (floor : Nat) (env : LEnv) (before : LS) :
    RhsOperandsAt floor env before curBlock := .of_blocks (by rw [curBlock_run])

theorem RhsOperandsAt.isLive (floor : Nat) (env : LEnv) (before : LS) :
    RhsOperandsAt floor env before isLive := .of_blocks rfl

theorem RhsOperandsAt.recordRead (floor : Nat) (env : LEnv) (before : LS) (value : ValueId) (place : Place) :
    RhsOperandsAt floor env before (recordReadValueRootRecipe value place) :=
  .of_blocks (recordReadValueRootRecipe_tables value place env before).1

theorem RhsOperandsAt.recordResult (floor : Nat) (env : LEnv) (before : LS) (value : ValueId) (scope : ScopeId) :
    RhsOperandsAt floor env before (recordValueRootRecipe value scope) :=
  .of_blocks (by rw [recordValueRootRecipe_run])

theorem RhsOperandsAt.whenLive {floor : Nat} {env : LEnv} {before : LS}
    (fallback : α) (action : BlockId → B α)
    (body : ∀ block, before.cur = some block → RhsOperandsAt floor env before (action block)) :
    RhsOperandsAt floor env before (whenLive fallback action) := by
  cases current : before.cur with
  | none => apply RhsOperandsAt.of_blocks; rw [whenLive_none _ _ _ current]
  | some block => simpa only [RhsOperandsAt, whenLive_some _ _ _ current] using body block current

theorem RhsOperandsAt.inScope {floor : Nat} {env : LEnv} {before : LS} {action : B α}
    (scope : ScopeId)
    (body : RhsOperandsAt floor env { before with stack := scope :: before.stack } action) :
    RhsOperandsAt floor env before (inScope scope action) := by
  let lowered := Goose.Lower.inScope scope action env before
  obtain ⟨middle, actionRun, same⟩ := inScope_eq
    (rfl : Goose.Lower.inScope scope action env before = lowered)
  have first : EmitsOnly (RhsUsesFresh floor) before { before with stack := scope :: before.stack } :=
    EmitsOnly.of_blocks rfl
  have inner : EmitsOnly (RhsUsesFresh floor) { before with stack := scope :: before.stack } middle := by
    change EmitsOnly (RhsUsesFresh floor) { before with stack := scope :: before.stack }
      (action env { before with stack := scope :: before.stack }).2 at body
    have output : (action env { before with stack := scope :: before.stack }).2 = middle :=
      congrArg Prod.snd actionRun
    rw [← output]
    exact body
  have blocks : lowered.2.blocks = middle.blocks := by
    have projected := congrArg LS.blocks same
    exact projected
  have last : EmitsOnly (RhsUsesFresh floor) middle lowered.2 := EmitsOnly.of_blocks blocks
  exact first.trans (inner.trans last)

end Goose.Lower.Validation
