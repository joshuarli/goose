import Goose.Lower.Validation.CfgReturnFreeBuilder

namespace Goose.Lower.Validation.SummaryPreservation.ReturnFrames

open Goose.Core Goose.GIR

variable {avoid : List ValueId × Option OriginId}

def ReturnAbsentCode {avoid : List ValueId × Option OriginId} (code : List Inst) : Prop :=
  .term (.ret avoid.1 avoid.2) ∉ code

theorem ReturnAbsentCode.nil : ReturnAbsentCode (avoid := avoid) [] := by simp [ReturnAbsentCode]

theorem ReturnAbsentCode.inst {code : List Inst} (prior : ReturnAbsentCode (avoid := avoid) code) (next : Inst)
    (ordinary : ∀ values origin, next ≠ .term (.ret values origin)) : ReturnAbsentCode (avoid := avoid) (code ++ [next]) := by
  intro member
  rcases List.mem_append.mp member with old | current
  · exact prior old
  · have same : .term (.ret avoid.1 avoid.2) = next := by simpa using current
    exact ordinary avoid.1 avoid.2 same.symm

def BuilderReturnAbsent {avoid : List ValueId × Option OriginId} (state : LS) : Prop :=
  ∀ (index : BlockId) (body : BlockB), state.blocks[index]? = some body →
    ReturnAbsentCode (avoid := avoid) body.insts.toList

theorem BuilderReturnAbsent.of_blocks {before after : LS}
    (checked : BuilderReturnAbsent (avoid := avoid) before) (blocks : after.blocks = before.blocks) :
    BuilderReturnAbsent (avoid := avoid) after := by
  intro index body row
  rw [blocks] at row
  exact checked index body row

theorem BuilderReturnAbsent.modify {state : LS}
    (checked : BuilderReturnAbsent (avoid := avoid) state) (index : BlockId) (update : BlockB → BlockB)
    (preserves : ∀ body, state.blocks[index]? = some body → ReturnAbsentCode (avoid := avoid) (update body).insts.toList) :
    BuilderReturnAbsent (avoid := avoid) { state with blocks := state.blocks.modify index update } := by
  intro position body row
  simp only [Array.getElem?_modify] at row
  by_cases same : index = position
  · simp only [same, ite_true, Option.map_eq_some_iff] at row
    obtain ⟨prior, found, rfl⟩ := row
    exact preserves prior (same ▸ found)
  · simp only [same, ite_false] at row
    exact checked position body row

theorem BuilderReturnAbsent.pushInst {state : LS}
    (checked : BuilderReturnAbsent (avoid := avoid) state) (index : BlockId) (inst : Inst)
    (ordinary : ∀ values origin, inst ≠ .term (.ret values origin)) (env : LEnv) :
    BuilderReturnAbsent (avoid := avoid) (pushInst index inst env state).2 := by
  apply checked.modify
  intro body row
  simpa using (checked index body row).inst inst ordinary

theorem BuilderReturnAbsent.emitDef {state : LS}
    (checked : BuilderReturnAbsent (avoid := avoid) state) (op : Op) (env : LEnv) :
    BuilderReturnAbsent (avoid := avoid) (emitDef op env state).2 := by
  cases current : state.cur with
  | none => rw [emitDef_none op env current]; exact checked
  | some block =>
    apply (checked.pushInst block (.def state.vals.size op) (by intro values origin same; cases same) env).of_blocks
    rw [emitDef_run op env current]
    rfl

theorem BuilderReturnAbsent.emitEffect {state : LS}
    (checked : BuilderReturnAbsent (avoid := avoid) state) (effect : Effect) (env : LEnv) :
    BuilderReturnAbsent (avoid := avoid) (emitEffect effect env state).2 := by
  cases current : state.cur with
  | none => rw [emitEffect_none effect env current]; exact checked
  | some block =>
    apply (checked.pushInst block (.eff effect) (by intro values origin same; cases same) env).of_blocks
    rw [emitEffect_run effect env current]
    rfl

theorem BuilderReturnAbsent.emitTerm {state : LS}
    (checked : BuilderReturnAbsent (avoid := avoid) state) (term : Term) (ordinary : ReturnFreeTerm term) (env : LEnv) :
    BuilderReturnAbsent (avoid := avoid) (emitTerm term env state).2 := by
  cases current : state.cur with
  | none => rw [emitTerm_none term env current]; exact checked
  | some block =>
    apply (checked.pushInst block (.term term) (by intro values origin same; exact ordinary values origin (Inst.term.inj same)) env).of_blocks
    rw [emitTerm_run term env current]
    rfl

theorem BuilderReturnAbsent.patchTerm {state : LS}
    (checked : BuilderReturnAbsent (avoid := avoid) state) (block : BlockId) (term : Term)
    (ordinary : ReturnFreeTerm term) (env : LEnv) : BuilderReturnAbsent (avoid := avoid) (patchTerm block term env state).2 :=
  checked.pushInst block (.term term) (by intro values origin same; exact ordinary values origin (Inst.term.inj same)) env

theorem BuilderReturnAbsent.newBlock {state : LS}
    (checked : BuilderReturnAbsent (avoid := avoid) state) (types : List VTy) (env : LEnv) :
    BuilderReturnAbsent (avoid := avoid) (newBlock types env state).2 := by
  intro index body row
  change (state.blocks.push _)[index]? = some body at row
  rw [Array.getElem?_push] at row
  split at row
  · have same := Option.some.inj row
    subst body
    exact .nil
  · exact checked index body row

theorem BuilderReturnAbsent.setCur {state : LS}
    (checked : BuilderReturnAbsent (avoid := avoid) state) (current : Option BlockId) (env : LEnv) :
    BuilderReturnAbsent (avoid := avoid) (setCur current env state).2 := checked.of_blocks rfl

def ReturnAbsentRun {avoid : List ValueId × Option OriginId} (action : B α) : Prop :=
  ∀ env before result after, action env before = (result, after) →
    BuilderReturnAbsent (avoid := avoid) before → BuilderReturnAbsent (avoid := avoid) after

theorem ReturnAbsentRun.pure (value : α) : ReturnAbsentRun (avoid := avoid) (pure value) := by
  intro env before result after run checked
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact checked

theorem ReturnAbsentRun.bind {first : B α} {next : α → B β}
    (one : ReturnAbsentRun (avoid := avoid) first) (two : ∀ value, ReturnAbsentRun (avoid := avoid) (next value)) : ReturnAbsentRun (avoid := avoid) (first >>= next) := by
  intro env before result after run checked
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  exact two value env middle result after nextRun (one env before value middle firstRun checked)

theorem ReturnAbsentRun.of_blocks {action : B α}
    (blocks : ∀ env state, (action env state).2.blocks = state.blocks) : ReturnAbsentRun (avoid := avoid) action := by
  intro env before result after run checked
  have same := blocks env before
  rw [run] at same
  exact checked.of_blocks same


end Goose.Lower.Validation.SummaryPreservation.ReturnFrames
