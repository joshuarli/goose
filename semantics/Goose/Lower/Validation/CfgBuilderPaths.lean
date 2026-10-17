import Goose.Lower.Validation.CfgTerminators
import Goose.Lower.Validation.CfgReachability

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

inductive BuilderPath (state : LS) : BlockId → Prop
  | entry : BuilderPath state 0
  | next {source target : BlockId} {body : BlockB}
      (prior : BuilderPath state source) (row : state.blocks[source]? = some body)
      (successor : target ∈ (cfgBlock body).terms.flatMap Term.successors)
      (bound : target < state.blocks.size) : BuilderPath state target

theorem BuilderPath.mono {before after : LS} (extension : before.Ext after)
    {block : BlockId} (path : BuilderPath before block) : BuilderPath after block := by
  induction path with
  | entry => exact .entry
  | @next source target body prior row successor bound ih =>
    obtain ⟨bodyNext, rowNext, _, extra, append⟩ := extension.2 source body row
    apply BuilderPath.next ih rowNext _ (Nat.lt_of_lt_of_le bound extension.1)
    have terms : (cfgBlock bodyNext).terms = (cfgBlock body).terms ++ extra.filterMap Inst.term? := by
      simp only [cfgBlock, GIR.Block.terms, append, List.filterMap_append]
    rw [terms, List.flatMap_append]
    exact List.mem_append_left _ successor

theorem BuilderPath.finished {state : LS} {block : BlockId} (path : BuilderPath state block)
    (func : Func) (blocks : func.blocks = finishBlocks state.blocks) : BlockReachable func block := by
  induction path with
  | entry => exact .entry
  | @next source target body prior row successor bound ih =>
    have finishedRow : func.blocks[source]? = some (cfgBlock body) := by
      simp [blocks, finishBlocks, cfgBlock, Array.getElem?_map, row]
    exact .next ih finishedRow successor (by simpa [blocks, finishBlocks] using bound)

def ReachableBuilder (state : LS) : Prop :=
  ∀ block, block < state.blocks.size → BuilderPath state block

theorem ReachableBuilder.of_ext {before after : LS} (paths : ReachableBuilder before)
    (extension : before.Ext after) (noNewBlocks : after.blocks.size ≤ before.blocks.size) :
    ReachableBuilder after := by
  intro block bound
  exact (paths block (Nat.lt_of_lt_of_le bound noNewBlocks)).mono extension

theorem ReachableBuilder.of_ext_one {before after : LS} (paths : ReachableBuilder before)
    (extension : before.Ext after) (oneNewBlock : after.blocks.size = before.blocks.size + 1)
    (newPath : BuilderPath after before.blocks.size) : ReachableBuilder after := by
  intro block bound
  by_cases old : block < before.blocks.size
  · exact (paths block old).mono extension
  · have equal : block = before.blocks.size := by
      omega
    exact equal ▸ newPath

theorem ReachableBuilder.emitDef {state : LS} (paths : ReachableBuilder state)
    (op : Op) (env : LEnv) : ReachableBuilder (Goose.Lower.emitDef op env state).2 := by
  have sameSize : (Goose.Lower.emitDef op env state).2.blocks.size = state.blocks.size := by
    cases current : state.cur with
    | none => rw [emitDef_none op env current]
    | some block => rw [emitDef_run op env current]; simp
  exact paths.of_ext (advB_emitDef op env state _ _ rfl).ext (Nat.le_of_eq sameSize)

theorem ReachableBuilder.emitEffect {state : LS} (paths : ReachableBuilder state)
    (effect : Effect) (env : LEnv) : ReachableBuilder (Goose.Lower.emitEffect effect env state).2 := by
  have sameSize : (Goose.Lower.emitEffect effect env state).2.blocks.size = state.blocks.size := by
    cases current : state.cur with
    | none => rw [emitEffect_none effect env current]
    | some block => rw [emitEffect_run effect env current]; simp
  exact paths.of_ext (advB_emitEffect effect env state _ _ rfl).ext (Nat.le_of_eq sameSize)

theorem ReachableBuilder.emitTerm {state : LS} (paths : ReachableBuilder state)
    (term : Term) (env : LEnv) : ReachableBuilder (Goose.Lower.emitTerm term env state).2 := by
  have sameSize : (Goose.Lower.emitTerm term env state).2.blocks.size = state.blocks.size := by
    cases current : state.cur with
    | none => rw [emitTerm_none term env current]
    | some block => rw [emitTerm_run term env current]; simp
  exact paths.of_ext (advB_emitTerm term env state _ _ rfl).ext (Nat.le_of_eq sameSize)

theorem ReachableBuilder.patchTerm {state : LS} (paths : ReachableBuilder state)
    (block : BlockId) (term : Term) (env : LEnv) :
    ReachableBuilder (patchTerm block term env state).2 := by
  rw [patchTerm_run]
  exact paths.of_ext ((LS.Ext.refl state).modify (appends_push _) block) (by simp)

theorem ReachableBuilder.finished {state : LS} (paths : ReachableBuilder state)
    (nonempty : 0 < state.blocks.size) (func : Func)
    (blocks : func.blocks = finishBlocks state.blocks) :
    ∀ block, block < func.blocks.size → (reachable func)[block]? = some true := by
  apply reachable_complete func (by simpa [blocks, finishBlocks] using nonempty)
  intro block bound
  exact (paths block (by simpa [blocks, finishBlocks] using bound)).finished func blocks

theorem ReachableBuilder.two_successors {before after : LS} (paths : ReachableBuilder before)
    (extension : before.Ext after) {source : BlockId} (sourceBound : source < before.blocks.size)
    (paramsFirst paramsSecond : List (ValueId × VTy)) (term : Term)
    (blocks : after.blocks = ((before.blocks.push ⟨paramsFirst, #[]⟩).push ⟨paramsSecond, #[]⟩).modify
      source (fun body => { body with insts := body.insts.push (.term term) }))
    (first : before.blocks.size ∈ term.successors)
    (second : before.blocks.size + 1 ∈ term.successors) : ReachableBuilder after := by
  have sourcePath := (paths source sourceBound).mono extension
  obtain ⟨body, bodyRow⟩ : ∃ body, before.blocks[source]? = some body :=
    ⟨before.blocks[source], Array.getElem?_eq_getElem sourceBound⟩
  have row : after.blocks[source]? = some { body with insts := body.insts.push (.term term) } := by
    rw [blocks]
    simp only [Array.getElem?_modify, ite_true, Option.map_eq_some_iff]
    refine ⟨body, ?_, rfl⟩
    simp [Array.getElem?_push, Nat.ne_of_lt sourceBound, bodyRow,
      (by nat_omega : source ≠ before.blocks.size + 1)]
  have nextPath : ∀ target ∈ term.successors, target < after.blocks.size → BuilderPath after target := by
    intro target member bound
    apply BuilderPath.next sourcePath row _ bound
    simp only [cfgBlock, GIR.Block.terms, Array.toList_push, List.filterMap_append,
      List.filterMap_cons, Inst.term?, List.filterMap_nil, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.mem_append_right _ member
  have afterSize : after.blocks.size = before.blocks.size + 2 := by simp [blocks, Nat.add_assoc]
  intro block bound
  by_cases old : block < before.blocks.size
  · exact (paths block old).mono extension
  · have equal : block = before.blocks.size ∨ block = before.blocks.size + 1 := by omega
    rcases equal with rfl | rfl
    · exact nextPath _ first (by omega)
    · exact nextPath _ second (by omega)

theorem ReachableBuilder.fork {state : LS} (paths : ReachableBuilder state)
    {source : BlockId} (current : state.cur = some source) (sourceBound : source < state.blocks.size)
    (condition : ValueId) (env : LEnv) : ReachableBuilder (fork condition env state).2 := by
  have table : (Goose.Lower.fork condition env state).2.blocks =
      ((state.blocks.push ⟨[], #[]⟩).push ⟨[], #[]⟩).modify source
        (fun body => { body with insts := body.insts.push (.term (.condbr condition state.blocks.size [] (state.blocks.size + 1) [])) }) := by
    rw [fork_run condition env current]
  exact paths.two_successors (adv_fork current rfl).ext sourceBound [] []
    (.condbr condition state.blocks.size [] (state.blocks.size + 1) []) table
    (by simp [Term.successors]) (by simp [Term.successors])

theorem ReachableBuilder.scFork {state : LS} (paths : ReachableBuilder state)
    {source : BlockId} (current : state.cur = some source) (sourceBound : source < state.blocks.size)
    (isAnd : Bool) (value : ValueId) (env : LEnv) :
    ReachableBuilder (scFork isAnd value env state).2 := by
  have table : (Goose.Lower.scFork isAnd value env state).2.blocks =
      ((state.blocks.push ⟨[], #[]⟩).push ⟨[(state.vals.size, .data .bool)], #[]⟩).modify source
        (fun body => { body with insts := body.insts.push (.term (scTerm isAnd value state.blocks.size (state.blocks.size + 1))) }) := by
    rw [scFork_run isAnd value env current]
  exact paths.two_successors (adv_scFork current rfl).ext sourceBound []
    [(state.vals.size, .data .bool)] (scTerm isAnd value state.blocks.size (state.blocks.size + 1)) table
    (by cases isAnd <;> simp [scTerm, Term.successors])
    (by cases isAnd <;> simp [scTerm, Term.successors])

end Goose.Lower.Validation
