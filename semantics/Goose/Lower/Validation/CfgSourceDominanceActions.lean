import Goose.Lower.Validation.CfgSourceDominanceBuilder
import Goose.Lower.Validate

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem LocalDefinitionBefore.append {body next : GIR.Block} {value index : Nat}
    (before : LocalDefinitionBefore body value index) (params : next.params = body.params)
    (extra : List Inst) (instructions : next.insts = body.insts ++ extra) :
    LocalDefinitionBefore next value index := by
  rcases before with parameter | ⟨prior, op, order, instruction⟩
  · exact Or.inl (params ▸ parameter)
  · refine Or.inr ⟨prior, op, order, ?_⟩
    have bound : prior < body.insts.length := (List.getElem?_eq_some_iff.mp instruction).1
    simpa only [instructions, List.getElem?_append_left bound] using instruction

theorem BuilderImportedSSA.of_blocks {before after : LS} {imports : ImportedValues}
    (certificate : BuilderImportedSSA before imports) (blocks : after.blocks = before.blocks) :
    BuilderImportedSSA after imports := by
  refine ⟨certificate.entry, ?_, ?_, ?_⟩
  · intro block body row
    exact certificate.foreign block body (by simpa [blocks] using row)
  · intro block body row
    exact certificate.operands block body (by simpa [blocks] using row)
  · intro block body row
    exact certificate.edges block body (by simpa [blocks] using row)

theorem BuilderImportedSSA.appendInst {state : LS} {imports : ImportedValues}
    (certificate : BuilderImportedSSA state imports) (block : BlockId) (inst : Inst)
    (fresh : ∀ value op, inst = .def value op → value ∉ imports block)
    (operands : ∀ body, state.blocks[block]? = some body → ∀ value ∈ inst.uses,
      value ∈ imports block ∨ LocalDefinitionBefore (cfgBlock body) value body.insts.size)
    (edges : ∀ body, state.blocks[block]? = some body → ∀ term, inst.term? = some term →
      ∀ target ∈ term.successors, ∀ value ∈ imports target,
        value ∈ imports block ∨ value ∈ (cfgBlock body).defs) :
    BuilderImportedSSA (state.appendInst block inst) imports := by
  let additional : List ValueId := match inst with
    | .def value _ => [value]
    | _ => []
  have appendedDefs (body : BlockB) :
      (cfgBlock { body with insts := body.insts.push inst }).defs =
        (cfgBlock body).defs ++ additional := by
    cases inst <;> simp [cfgBlock, GIR.Block.defs, List.filterMap_append,
      additional, List.append_assoc]
  have defs {body : BlockB} {value : Nat}
      (defined : value ∈ (cfgBlock { body with insts := body.insts.push inst }).defs) :
      value ∈ (cfgBlock body).defs ∨ ∃ op, inst = .def value op := by
    rw [appendedDefs] at defined
    rcases List.mem_append.mp defined with old | new
    · exact Or.inl old
    · cases inst with
      | «def» result op =>
        have equal : value = result := by simpa [additional] using new
        exact Or.inr ⟨op, by simp [equal]⟩
      | eff effect => simp [additional] at new
      | term term => simp [additional] at new
  have priorDefs {body : BlockB} {value : Nat} (defined : value ∈ (cfgBlock body).defs) :
      value ∈ (cfgBlock { body with insts := body.insts.push inst }).defs := by
    rw [appendedDefs]
    exact List.mem_append_left _ defined
  refine ⟨certificate.entry, ?_, ?_, ?_⟩
  · intro index body row value imported defined
    change (state.blocks.modify block _)[index]? = some body at row
    simp only [Array.getElem?_modify] at row
    split at row
    · rename_i same
      subst index
      obtain ⟨previous, previousRow, rfl⟩ := Option.map_eq_some_iff.mp row
      rcases defs defined with old | ⟨op, equal⟩
      · exact certificate.foreign block previous previousRow value imported old
      · exact fresh value op equal imported
    · exact certificate.foreign index body row value imported defined
  · intro index body row position instruction instructionAt value used
    change (state.blocks.modify block _)[index]? = some body at row
    simp only [Array.getElem?_modify] at row
    split at row
    · rename_i same
      subst index
      obtain ⟨previous, previousRow, rfl⟩ := Option.map_eq_some_iff.mp row
      change (previous.insts.push inst)[position]? = some instruction at instructionAt
      by_cases old : position < previous.insts.size
      · have prior : previous.insts[position]? = some instruction := by
          simpa only [Array.getElem?_push, old, Nat.ne_of_lt old, ite_false] using instructionAt
        rcases certificate.operands block previous previousRow position instruction prior value used with
          imported | localBefore
        · exact Or.inl imported
        · exact Or.inr (localBefore.append rfl [inst] (by simp [cfgBlock]))
      · have equal : position = previous.insts.size := by
          have bound := (Array.getElem?_eq_some_iff.mp instructionAt).1
          simp only [Array.size_push] at bound
          omega
        subst position
        have equal : inst = instruction := by simpa using instructionAt
        subst instruction
        rcases operands previous previousRow value used with imported | localBefore
        · exact Or.inl imported
        · exact Or.inr (localBefore.append rfl [inst] (by simp [cfgBlock]))
    · exact certificate.operands index body row position instruction instructionAt value used
  · intro source body row target successor value imported
    change (state.blocks.modify block _)[source]? = some body at row
    simp only [Array.getElem?_modify] at row
    split at row
    · rename_i same
      subst source
      obtain ⟨previous, previousRow, rfl⟩ := Option.map_eq_some_iff.mp row
      simp only [cfgBlock, GIR.Block.terms, Array.toList_push, List.filterMap_append,
        List.flatMap_append, List.mem_append] at successor
      have transported : value ∈ imports block ∨ value ∈ (cfgBlock previous).defs := by
        rcases successor with old | new
        · exact certificate.edges block previous previousRow target old value imported
        · cases termRow : inst.term? with
          | none => simp [termRow] at new
          | some targetTerm =>
            exact edges previous previousRow targetTerm termRow target
              (by simpa [termRow] using new) value imported
      exact transported.imp_right priorDefs
    · exact certificate.edges source body row target successor value imported

theorem BuilderImportedSSA.emitDef {state : LS} {imports : ImportedValues}
    (certificate : BuilderImportedSSA state imports) (op : Op) (env : LEnv)
    (fresh : ∀ block, state.cur = some block → state.vals.size ∉ imports block)
    (operands : ∀ block, state.cur = some block → ∀ value ∈ op.uses,
      BuilderAvailable state imports block value) :
    BuilderImportedSSA (emitDef op env state).2 imports := by
  cases current : state.cur with
  | none => rw [emitDef_none op env current]; exact certificate
  | some block =>
    have appended := certificate.appendInst block (.def state.vals.size op)
      (by intro value operation equal; cases equal; exact fresh block current)
      (by
        intro body row value used
        obtain ⟨previous, previousRow, available⟩ :=
          (operands block current value used).before_end
        have equal := Option.some.inj (row.symm.trans previousRow)
        subst previous
        exact available)
      (by intro body row term found; cases found)
    apply appended.of_blocks
    rw [emitDef_run op env current]
    rfl

theorem BuilderImportedSSA.emitEffect {state : LS} {imports : ImportedValues}
    (certificate : BuilderImportedSSA state imports) (effect : Effect) (env : LEnv)
    (operands : ∀ block, state.cur = some block → ∀ value ∈ effect.uses,
      BuilderAvailable state imports block value) :
    BuilderImportedSSA (emitEffect effect env state).2 imports := by
  cases current : state.cur with
  | none => rw [emitEffect_none effect env current]; exact certificate
  | some block =>
    have appended := certificate.appendInst block (.eff effect)
      (by intro value operation equal; cases equal)
      (by
        intro body row value used
        obtain ⟨previous, previousRow, available⟩ :=
          (operands block current value used).before_end
        have equal := Option.some.inj (row.symm.trans previousRow)
        subst previous
        exact available)
      (by intro body row term found; cases found)
    apply appended.of_blocks
    rw [emitEffect_run effect env current]
    rfl

theorem BuilderImportedSSA.patchTerm {state : LS} {imports : ImportedValues}
    (certificate : BuilderImportedSSA state imports) (block : BlockId) (term : Term) (env : LEnv)
    (operands : ∀ value ∈ term.uses, BuilderAvailable state imports block value)
    (edges : ∀ target ∈ term.successors, ∀ value ∈ imports target,
      BuilderAvailable state imports block value) :
    BuilderImportedSSA (patchTerm block term env state).2 imports := by
  have appended := certificate.appendInst block (.term term)
    (by intro value operation equal; cases equal)
    (by
      intro body row value used
      obtain ⟨previous, previousRow, available⟩ := (operands value used).before_end
      have equal := Option.some.inj (row.symm.trans previousRow)
      subst previous
      exact available)
    (by
      intro body row operation found target successor value imported
      cases found
      obtain ⟨previous, previousRow, available⟩ := edges target successor value imported
      have equal := Option.some.inj (row.symm.trans previousRow)
      subst previous
      exact available)
  exact appended.of_blocks (by rw [patchTerm_run]; rfl)

theorem BuilderImportedSSA.emitTerm {state : LS} {imports : ImportedValues}
    (certificate : BuilderImportedSSA state imports) (term : Term) (env : LEnv)
    (operands : ∀ block, state.cur = some block → ∀ value ∈ term.uses,
      BuilderAvailable state imports block value)
    (edges : ∀ block, state.cur = some block → ∀ target ∈ term.successors,
      ∀ value ∈ imports target, BuilderAvailable state imports block value) :
    BuilderImportedSSA (emitTerm term env state).2 imports := by
  cases current : state.cur with
  | none => rw [emitTerm_none term env current]; exact certificate
  | some block =>
    have patched := certificate.patchTerm block term env
      (operands block current) (edges block current)
    apply patched.of_blocks
    rw [patchTerm_run, emitTerm_run term env current]

end Goose.Lower.Validation
