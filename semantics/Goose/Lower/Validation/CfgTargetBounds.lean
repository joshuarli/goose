import Goose.Lower.Validation.CfgTerminators

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def TargetsBounded (state : LS) : Prop :=
  ∀ (index : BlockId) (body : BlockB), state.blocks[index]? = some body →
    ∀ target ∈ (cfgBlock body).terms.flatMap Term.successors, target < state.blocks.size

theorem TargetsBounded.of_blocks {before after : LS} (bounded : TargetsBounded before)
    (blocks : after.blocks = before.blocks) : TargetsBounded after := by
  intro index body row target successor
  rw [blocks] at row ⊢
  exact bounded index body row target successor

theorem TargetsBounded.modify {state : LS} (bounded : TargetsBounded state) (index : BlockId)
    (change : BlockB → BlockB)
    (preserves : ∀ body, state.blocks[index]? = some body →
      ∀ target ∈ (cfgBlock (change body)).terms.flatMap Term.successors,
        target < state.blocks.size) :
    TargetsBounded { state with blocks := state.blocks.modify index change } := by
  intro position body row target successor
  simp only [Array.getElem?_modify] at row
  by_cases same : index = position
  · simp only [same, ite_true, Option.map_eq_some_iff] at row
    obtain ⟨prior, found, rfl⟩ := row
    simpa using preserves prior (same ▸ found) target successor
  · simp only [same, ite_false] at row
    simpa using bounded position body row target successor

theorem TargetsBounded.pushInst {state : LS} (bounded : TargetsBounded state) (index : BlockId)
    (inst : Inst) (targets : ∀ term, inst.term? = some term →
      ∀ target ∈ term.successors, target < state.blocks.size) (env : LEnv) :
    TargetsBounded (pushInst index inst env state).2 := by
  change TargetsBounded { state with blocks := state.blocks.modify index (fun body => { body with insts := body.insts.push inst }) }
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

theorem TargetsBounded.emitDef {state : LS} (bounded : TargetsBounded state) (op : Op) (env : LEnv) :
    TargetsBounded (emitDef op env state).2 := by
  cases current : state.cur with
  | none => rw [emitDef_none op env current]; exact bounded
  | some block =>
    have pushed := bounded.pushInst block (.def state.vals.size op)
      (by intro term found; cases found) env
    apply pushed.of_blocks
    rw [emitDef_run op env current]
    rfl

theorem TargetsBounded.emitEffect {state : LS} (bounded : TargetsBounded state)
    (effect : Effect) (env : LEnv) : TargetsBounded (emitEffect effect env state).2 := by
  cases current : state.cur with
  | none => rw [emitEffect_none effect env current]; exact bounded
  | some block =>
    have pushed := bounded.pushInst block (.eff effect) (by intro term found; cases found) env
    apply pushed.of_blocks
    rw [emitEffect_run effect env current]
    rfl

theorem TargetsBounded.emitTerm {state : LS} (bounded : TargetsBounded state) (term : Term)
    (targets : ∀ target ∈ term.successors, target < state.blocks.size) (env : LEnv) :
    TargetsBounded (emitTerm term env state).2 := by
  cases current : state.cur with
  | none => rw [emitTerm_none term env current]; exact bounded
  | some block =>
    have pushed := bounded.pushInst block (.term term)
      (by intro value found; cases found; exact targets) env
    apply pushed.of_blocks
    rw [emitTerm_run term env current]
    rfl

theorem TargetsBounded.patchTerm {state : LS} (bounded : TargetsBounded state) (block : BlockId)
    (term : Term) (targets : ∀ target ∈ term.successors, target < state.blocks.size) (env : LEnv) :
    TargetsBounded (patchTerm block term env state).2 :=
  bounded.pushInst block (.term term) (by intro value found; cases found; exact targets) env

theorem TargetsBounded.newBlock {state : LS} (bounded : TargetsBounded state)
    (types : List VTy) (env : LEnv) : TargetsBounded (newBlock types env state).2 := by
  intro position body row target successor
  change (state.blocks.push ⟨((List.range types.length).map (state.vals.size + ·)).zip types, #[]⟩)[position]? =
    some body at row
  rw [Array.getElem?_push] at row
  by_cases fresh : position = state.blocks.size
  · simp only [fresh, ite_true, Option.some.injEq] at row
    subst body
    simp [cfgBlock, GIR.Block.terms] at successor
  · simp only [fresh, ite_false] at row
    have old := bounded position body row target successor
    change target < (state.blocks.push _).size
    simp only [Array.size_push]
    exact Nat.lt_trans old (Nat.lt_succ_self _)

theorem TargetsBounded.setCur {state : LS} (bounded : TargetsBounded state)
    (current : Option BlockId) (env : LEnv) : TargetsBounded (setCur current env state).2 :=
  bounded.of_blocks rfl

end Goose.Lower.Validation
