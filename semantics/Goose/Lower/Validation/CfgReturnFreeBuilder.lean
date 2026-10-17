import Goose.Lower.Validation.CfgReturnCode
import Goose.Lower.Validation.CfgReturnFreeSyntax

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def ReturnFreeTerm (term : Term) : Prop := ∀ values origin, term ≠ .ret values origin

theorem NoReturnCode.nil : NoReturnCode [] := by intro values origin; simp

theorem NoReturnCode.inst {code : List Inst} (prior : NoReturnCode code) (next : Inst)
    (ordinary : ∀ values origin, next ≠ .term (.ret values origin)) : NoReturnCode (code ++ [next]) := by
  intro values origin member
  rcases List.mem_append.mp member with old | current
  · exact prior values origin old
  · have same : .term (.ret values origin) = next := by simpa using current
    exact ordinary values origin same.symm

def BuilderNoReturn (state : LS) : Prop :=
  ∀ (index : BlockId) (body : BlockB), state.blocks[index]? = some body →
    NoReturnCode body.insts.toList

theorem BuilderNoReturn.of_blocks {before after : LS}
    (checked : BuilderNoReturn before) (blocks : after.blocks = before.blocks) :
    BuilderNoReturn after := by
  intro index body row
  rw [blocks] at row
  exact checked index body row

theorem BuilderNoReturn.modify {state : LS}
    (checked : BuilderNoReturn state) (index : BlockId) (update : BlockB → BlockB)
    (preserves : ∀ body, state.blocks[index]? = some body → NoReturnCode (update body).insts.toList) :
    BuilderNoReturn { state with blocks := state.blocks.modify index update } := by
  intro position body row
  simp only [Array.getElem?_modify] at row
  by_cases same : index = position
  · simp only [same, ite_true, Option.map_eq_some_iff] at row
    obtain ⟨prior, found, rfl⟩ := row
    exact preserves prior (same ▸ found)
  · simp only [same, ite_false] at row
    exact checked position body row

theorem BuilderNoReturn.pushInst {state : LS}
    (checked : BuilderNoReturn state) (index : BlockId) (inst : Inst)
    (ordinary : ∀ values origin, inst ≠ .term (.ret values origin)) (env : LEnv) :
    BuilderNoReturn (pushInst index inst env state).2 := by
  apply checked.modify
  intro body row
  simpa using (checked index body row).inst inst ordinary

theorem BuilderNoReturn.emitDef {state : LS}
    (checked : BuilderNoReturn state) (op : Op) (env : LEnv) :
    BuilderNoReturn (emitDef op env state).2 := by
  cases current : state.cur with
  | none => rw [emitDef_none op env current]; exact checked
  | some block =>
    apply (checked.pushInst block (.def state.vals.size op) (by intro values origin same; cases same) env).of_blocks
    rw [emitDef_run op env current]
    rfl

theorem BuilderNoReturn.emitEffect {state : LS}
    (checked : BuilderNoReturn state) (effect : Effect) (env : LEnv) :
    BuilderNoReturn (emitEffect effect env state).2 := by
  cases current : state.cur with
  | none => rw [emitEffect_none effect env current]; exact checked
  | some block =>
    apply (checked.pushInst block (.eff effect) (by intro values origin same; cases same) env).of_blocks
    rw [emitEffect_run effect env current]
    rfl

theorem BuilderNoReturn.emitTerm {state : LS}
    (checked : BuilderNoReturn state) (term : Term) (ordinary : ReturnFreeTerm term) (env : LEnv) :
    BuilderNoReturn (emitTerm term env state).2 := by
  cases current : state.cur with
  | none => rw [emitTerm_none term env current]; exact checked
  | some block =>
    apply (checked.pushInst block (.term term) (by intro values origin same; exact ordinary values origin (Inst.term.inj same)) env).of_blocks
    rw [emitTerm_run term env current]
    rfl

theorem BuilderNoReturn.patchTerm {state : LS}
    (checked : BuilderNoReturn state) (block : BlockId) (term : Term)
    (ordinary : ReturnFreeTerm term) (env : LEnv) : BuilderNoReturn (patchTerm block term env state).2 :=
  checked.pushInst block (.term term) (by intro values origin same; exact ordinary values origin (Inst.term.inj same)) env

theorem BuilderNoReturn.newBlock {state : LS}
    (checked : BuilderNoReturn state) (types : List VTy) (env : LEnv) :
    BuilderNoReturn (newBlock types env state).2 := by
  intro index body row
  change (state.blocks.push _)[index]? = some body at row
  rw [Array.getElem?_push] at row
  split at row
  · have same := Option.some.inj row
    subst body
    exact .nil
  · exact checked index body row

theorem BuilderNoReturn.setCur {state : LS}
    (checked : BuilderNoReturn state) (current : Option BlockId) (env : LEnv) :
    BuilderNoReturn (setCur current env state).2 := checked.of_blocks rfl

def ReturnFreeRun (action : B α) : Prop :=
  ∀ env before result after, action env before = (result, after) →
    BuilderNoReturn before → BuilderNoReturn after

theorem ReturnFreeRun.pure (value : α) : ReturnFreeRun (pure value) := by
  intro env before result after run checked
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact checked

theorem ReturnFreeRun.bind {first : B α} {next : α → B β}
    (one : ReturnFreeRun first) (two : ∀ value, ReturnFreeRun (next value)) : ReturnFreeRun (first >>= next) := by
  intro env before result after run checked
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  exact two value env middle result after nextRun (one env before value middle firstRun checked)

theorem ReturnFreeRun.of_blocks {action : B α}
    (blocks : ∀ env state, (action env state).2.blocks = state.blocks) : ReturnFreeRun action := by
  intro env before result after run checked
  have same := blocks env before
  rw [run] at same
  exact checked.of_blocks same


end Goose.Lower.Validation
