import Goose.Lower.Frag
import Goose.GIR.Validate

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def cfgBlock (block : BlockB) : GIR.Block :=
  ⟨block.params, block.insts.toList⟩

def OpenBlock (block : BlockB) : Prop := (cfgBlock block).terms = []

def ClosedBlock (block : BlockB) : Prop :=
  (cfgBlock block).terms.length = 1 ∧ (cfgBlock block).lastTerm?.isSome = true

theorem open_empty (params : List (ValueId × VTy)) : OpenBlock ⟨params, #[]⟩ := rfl

theorem open_push_def {block : BlockB} (openBlock : OpenBlock block) (value : ValueId) (op : Op) :
    OpenBlock { block with insts := block.insts.push (.def value op) } := by
  simpa [OpenBlock, cfgBlock, GIR.Block.terms, List.filterMap_append, Inst.term?]
    using openBlock

theorem open_push_effect {block : BlockB} (openBlock : OpenBlock block) (effect : Effect) :
    OpenBlock { block with insts := block.insts.push (.eff effect) } := by
  simpa [OpenBlock, cfgBlock, GIR.Block.terms, List.filterMap_append, Inst.term?]
    using openBlock

theorem open_push_term {block : BlockB} (openBlock : OpenBlock block) (term : Term) :
    ClosedBlock { block with insts := block.insts.push (.term term) } := by
  have noTerms : block.insts.toList.filterMap Inst.term? = [] := openBlock
  simp [ClosedBlock, cfgBlock, GIR.Block.terms, GIR.Block.lastTerm?,
    List.filterMap_append, Inst.term?, noTerms]

theorem emitDef_open {state : LS} {block : BlockId} {body : BlockB}
    (current : state.cur = some block) (row : state.blocks[block]? = some body)
    (openBlock : OpenBlock body) (op : Op) (env : LEnv) :
    ∃ next, (emitDef op env state).2.blocks[block]? = some next ∧ OpenBlock next := by
  rw [emitDef_run op env current]
  refine ⟨{ body with insts := body.insts.push (.def state.vals.size op) }, ?_,
    open_push_def openBlock _ _⟩
  simp [Array.getElem?_modify, row]

theorem emitEffect_open {state : LS} {block : BlockId} {body : BlockB}
    (current : state.cur = some block) (row : state.blocks[block]? = some body)
    (openBlock : OpenBlock body) (effect : Effect) (env : LEnv) :
    ∃ next, (emitEffect effect env state).2.blocks[block]? = some next ∧ OpenBlock next := by
  rw [emitEffect_run effect env current]
  refine ⟨{ body with insts := body.insts.push (.eff effect) }, ?_,
    open_push_effect openBlock _⟩
  simp [Array.getElem?_modify, row]

theorem emitTerm_closed {state : LS} {block : BlockId} {body : BlockB}
    (current : state.cur = some block) (row : state.blocks[block]? = some body)
    (openBlock : OpenBlock body) (term : Term) (env : LEnv) :
    (emitTerm term env state).2.cur = none ∧
    ∃ next, (emitTerm term env state).2.blocks[block]? = some next ∧ ClosedBlock next := by
  rw [emitTerm_run term env current]
  refine ⟨rfl, { body with insts := body.insts.push (.term term) }, ?_,
    open_push_term openBlock _⟩
  simp [Array.getElem?_modify, row]

theorem patchTerm_closed {state : LS} {block : BlockId} {body : BlockB}
    (row : state.blocks[block]? = some body) (openBlock : OpenBlock body)
    (term : Term) (env : LEnv) :
    ∃ next, (patchTerm block term env state).2.blocks[block]? = some next ∧ ClosedBlock next := by
  rw [patchTerm_run]
  refine ⟨{ body with insts := body.insts.push (.term term) }, ?_,
    open_push_term openBlock _⟩
  simp [Array.getElem?_modify, row]

theorem patchTerm_other (state : LS) (env : LEnv) (block other : BlockId)
    (distinct : block ≠ other) (term : Term) :
    (patchTerm block term env state).2.blocks[other]? = state.blocks[other]? := by
  rw [patchTerm_run]
  simp [Array.getElem?_modify, distinct]

theorem newBlock_open (state : LS) (env : LEnv) (types : List VTy) :
    ∃ body, (newBlock types env state).2.blocks[state.blocks.size]? = some body ∧ OpenBlock body := by
  refine ⟨⟨((List.range types.length).map (state.vals.size + ·)).zip types, #[]⟩, ?_, open_empty _⟩
  change (state.blocks.push _)[state.blocks.size]? = _
  simp

theorem newBlock_other (state : LS) (env : LEnv) (types : List VTy) (block : BlockId)
    (old : block < state.blocks.size) :
    (newBlock types env state).2.blocks[block]? = state.blocks[block]? := by
  change (state.blocks.push _)[block]? = _
  simp [Array.getElem?_push, old, Nat.ne_of_lt old]

private theorem cfg_checkAll_ok {items : List α} {action : α → Except ε Unit}
    (accepted : ∀ item ∈ items, action item = .ok ()) : checkAll items action = .ok () := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [checkAll, accepted item (by simp), bind, Except.bind]
    exact ih fun next member => accepted next (by simp [member])

theorem finishBlocks_terminators (blocks : Array BlockB)
    (closed : ∀ block ∈ blocks.toList, ClosedBlock block) (label : String) :
    (checkAll (finishBlocks blocks).toList.zipIdx fun (block, index) => do
      unless block.terms.length = 1 do
        violation .v020 s!"{label}: block {index} has {block.terms.length} terminators, expected one"
      if block.lastTerm?.isNone then
        violation .v020 s!"{label}: block {index} does not end in its terminator") = .ok () := by
  apply cfg_checkAll_ok
  intro pair member
  have present : pair.1 ∈ (finishBlocks blocks).toList := List.fst_mem_of_mem_zipIdx member
  have mapped : ∃ block ∈ blocks.toList, (cfgBlock block) = pair.1 := by
    simpa [finishBlocks, cfgBlock] using present
  obtain ⟨block, member, same⟩ := mapped
  have shape := closed block member
  have termCount : pair.1.terms.length = 1 := by rw [← same]; exact shape.1
  have termLast : pair.1.lastTerm?.isNone = false := by
    rw [← same]
    cases last : (cfgBlock block).lastTerm? <;> simp_all [ClosedBlock]
  simp [termCount, termLast, pure, Except.pure]

end Goose.Lower.Validation
