import Goose.Lower.Validation.CfgFrontier
import Goose.Lower.Validation.CfgTerminators

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def TargetsNonzero (state : LS) : Prop :=
  ∀ (index : BlockId) (body : BlockB), state.blocks[index]? = some body →
    ∀ target ∈ (cfgBlock body).terms.flatMap Term.successors, target ≠ 0

theorem TargetsNonzero.of_blocks {before after : LS} (bounded : TargetsNonzero before)
    (blocks : after.blocks = before.blocks) : TargetsNonzero after := by
  intro index body row target successor
  rw [blocks] at row
  exact bounded index body row target successor

theorem TargetsNonzero.modify {state : LS} (bounded : TargetsNonzero state) (index : BlockId)
    (change : BlockB → BlockB)
    (preserves : ∀ body, state.blocks[index]? = some body →
      ∀ target ∈ (cfgBlock (change body)).terms.flatMap Term.successors,
        target ≠ 0) :
    TargetsNonzero { state with blocks := state.blocks.modify index change } := by
  intro position body row target successor
  simp only [Array.getElem?_modify] at row
  by_cases same : index = position
  · simp only [same, ite_true, Option.map_eq_some_iff] at row
    obtain ⟨prior, found, rfl⟩ := row
    simpa using preserves prior (same ▸ found) target successor
  · simp only [same, ite_false] at row
    simpa using bounded position body row target successor

theorem TargetsNonzero.pushInst {state : LS} (bounded : TargetsNonzero state) (index : BlockId)
    (inst : Inst) (targets : ∀ term, inst.term? = some term →
      ∀ target ∈ term.successors, target ≠ 0) (env : LEnv) :
    TargetsNonzero (pushInst index inst env state).2 := by
  change TargetsNonzero { state with blocks := state.blocks.modify index (fun body => { body with insts := body.insts.push inst }) }
  apply bounded.modify
  intro body row target successor
  simp only [cfgBlock, GIR.Block.terms, Array.toList_push, List.filterMap_append,
    List.flatMap_append, List.mem_append] at successor
  rcases successor with old | new
  · exact bounded index body row target old
  · cases term : inst.term? with
    | none => simp [term] at new
    | some value =>
      have member : target ∈ value.successors := by simpa [term] using new
      exact targets value term target member

theorem TargetsNonzero.emitDef {state : LS} (bounded : TargetsNonzero state) (op : Op) (env : LEnv) :
    TargetsNonzero (emitDef op env state).2 := by
  cases current : state.cur with
  | none => rw [emitDef_none op env current]; exact bounded
  | some block =>
    have pushed := bounded.pushInst block (.def state.vals.size op)
      (by intro term found; cases found) env
    apply pushed.of_blocks
    rw [emitDef_run op env current]
    rfl

theorem TargetsNonzero.emitEffect {state : LS} (bounded : TargetsNonzero state)
    (effect : Effect) (env : LEnv) : TargetsNonzero (emitEffect effect env state).2 := by
  cases current : state.cur with
  | none => rw [emitEffect_none effect env current]; exact bounded
  | some block =>
    have pushed := bounded.pushInst block (.eff effect) (by intro term found; cases found) env
    apply pushed.of_blocks
    rw [emitEffect_run effect env current]
    rfl

theorem TargetsNonzero.emitTerm {state : LS} (bounded : TargetsNonzero state) (term : Term)
    (targets : ∀ target ∈ term.successors, target ≠ 0) (env : LEnv) :
    TargetsNonzero (emitTerm term env state).2 := by
  cases current : state.cur with
  | none => rw [emitTerm_none term env current]; exact bounded
  | some block =>
    have pushed := bounded.pushInst block (.term term)
      (by intro value found; cases found; exact targets) env
    apply pushed.of_blocks
    rw [emitTerm_run term env current]
    rfl

theorem TargetsNonzero.patchTerm {state : LS} (bounded : TargetsNonzero state) (block : BlockId)
    (term : Term) (targets : ∀ target ∈ term.successors, target ≠ 0) (env : LEnv) :
    TargetsNonzero (patchTerm block term env state).2 :=
  bounded.pushInst block (.term term) (by intro value found; cases found; exact targets) env

theorem TargetsNonzero.newBlock {state : LS} (bounded : TargetsNonzero state)
    (types : List VTy) (env : LEnv) : TargetsNonzero (newBlock types env state).2 := by
  intro position body row target successor
  change (state.blocks.push ⟨((List.range types.length).map (state.vals.size + ·)).zip types, #[]⟩)[position]? =
    some body at row
  rw [Array.getElem?_push] at row
  by_cases fresh : position = state.blocks.size
  · simp only [fresh, ite_true, Option.some.injEq] at row
    subst body
    simp [cfgBlock, GIR.Block.terms] at successor
  · simp only [fresh, ite_false] at row
    exact bounded position body row target successor

theorem TargetsNonzero.setCur {state : LS} (bounded : TargetsNonzero state)
    (current : Option BlockId) (env : LEnv) : TargetsNonzero (setCur current env state).2 :=
  bounded.of_blocks rfl

def EntryTargets (state : LS) : Prop :=
  0 < state.blocks.size ∧ TargetsNonzero state

theorem EntryTargets.positive {state : LS} (checked : EntryTargets state) : 0 < state.blocks.size := checked.1

theorem EntryTargets.nonzero {state : LS} (checked : EntryTargets state) : TargetsNonzero state := checked.2

theorem EntryTargets.of_advance {before after : LS} (checked : EntryTargets before)
    (advance : before.Adv after) (targets : TargetsNonzero after) : EntryTargets after :=
  ⟨Nat.lt_of_lt_of_le checked.positive advance.ext.1, targets⟩

theorem EntryTargets.emitDef {state : LS} (checked : EntryTargets state) (op : Op) (env : LEnv) :
    EntryTargets (emitDef op env state).2 :=
  checked.of_advance (advB_emitDef op env state _ _ rfl) (checked.nonzero.emitDef op env)

theorem EntryTargets.emitEffect {state : LS} (checked : EntryTargets state) (effect : Effect) (env : LEnv) :
    EntryTargets (emitEffect effect env state).2 :=
  checked.of_advance (advB_emitEffect effect env state _ _ rfl) (checked.nonzero.emitEffect effect env)

theorem EntryTargets.emitTerm {state : LS} (checked : EntryTargets state) (term : Term)
    (targets : ∀ target ∈ term.successors, target ≠ 0) (env : LEnv) : EntryTargets (emitTerm term env state).2 :=
  checked.of_advance (advB_emitTerm term env state _ _ rfl) (checked.nonzero.emitTerm term targets env)

theorem EntryTargets.patchTerm {state : LS} (checked : EntryTargets state) (block : BlockId)
    (term : Term) (targets : ∀ target ∈ term.successors, target ≠ 0) (env : LEnv) :
    EntryTargets (patchTerm block term env state).2 :=
  ⟨by rw [patchTerm_run]; simpa using checked.positive, checked.nonzero.patchTerm block term targets env⟩

theorem EntryTargets.newBlock {state : LS} (checked : EntryTargets state) (types : List VTy) (env : LEnv) :
    EntryTargets (newBlock types env state).2 :=
  ⟨by change 0 < (state.blocks.push _).size; simp, checked.nonzero.newBlock types env⟩

theorem EntryTargets.setCur {state : LS} (checked : EntryTargets state) (current : Option BlockId) (env : LEnv) :
    EntryTargets (setCur current env state).2 := ⟨checked.positive, checked.nonzero.setCur current env⟩

theorem EntryTargets.of_blocks {before after : LS} (checked : EntryTargets before)
    (same : after.blocks = before.blocks) : EntryTargets after :=
  ⟨same ▸ checked.positive, checked.nonzero.of_blocks same⟩

end Goose.Lower.Validation
