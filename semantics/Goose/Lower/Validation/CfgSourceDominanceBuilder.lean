import Goose.Lower.Validation.CfgSourceDominanceCertificate

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def BuilderAvailable (state : LS) (imports : ImportedValues) (block value : Nat) : Prop :=
  ∃ body, state.blocks[block]? = some body ∧
    (value ∈ imports block ∨ value ∈ (cfgBlock body).defs)

def BuilderBefore (state : LS) (imports : ImportedValues) (block value index : Nat) : Prop :=
  ∃ body, state.blocks[block]? = some body ∧
    (value ∈ imports block ∨ LocalDefinitionBefore (cfgBlock body) value index)

structure BuilderImportedSSA (state : LS) (imports : ImportedValues) : Prop where
  entry : imports 0 = []
  foreign : ∀ block body, state.blocks[block]? = some body →
    ∀ value ∈ imports block, value ∉ (cfgBlock body).defs
  operands : ∀ block body, state.blocks[block]? = some body → ∀ index inst,
    body.insts[index]? = some inst → ∀ value ∈ inst.uses,
      value ∈ imports block ∨ LocalDefinitionBefore (cfgBlock body) value index
  edges : ∀ source body, state.blocks[source]? = some body →
    ∀ target ∈ (cfgBlock body).terms.flatMap Term.successors,
      ∀ value ∈ imports target, value ∈ imports source ∨ value ∈ (cfgBlock body).defs

theorem BuilderImportedSSA.finished {state : LS} {imports : ImportedValues}
    (certificate : BuilderImportedSSA state imports) (func : Func)
    (blocks : func.blocks = finishBlocks state.blocks) : ImportedSSA func imports := by
  have row : ∀ {block : BlockId} {body : GIR.Block}, func.blocks[block]? = some body →
      ∃ builder, state.blocks[block]? = some builder ∧ cfgBlock builder = body := by
    intro block body found
    simpa only [blocks, finishBlocks, Array.getElem?_map, Option.map_eq_some_iff,
      cfgBlock] using found
  refine ⟨certificate.entry, ?_, ?_, ?_⟩
  · intro block body found value imported
    obtain ⟨builder, builderRow, rfl⟩ := row found
    exact certificate.foreign block builder builderRow value imported
  · intro block bound inst index present value operand
    have found : func.blocks[block]? = some func.blocks[block] := Array.getElem?_eq_getElem bound
    obtain ⟨builder, builderRow, same⟩ := row found
    have instruction := List.mk_mem_zipIdx_iff_getElem?.mp present
    have instructionBuilder : builder.insts[index]? = some inst := by
      simpa only [← same, cfgBlock, Array.getElem?_toList] using instruction
    have available := certificate.operands block builder builderRow index inst instructionBuilder value operand
    simpa only [same] using available
  · intro target source body predecessor found value imported
    obtain ⟨sourceBody, sourceRow, successor⟩ := predecessor_origin func predecessor
    have equal : sourceBody = body := Option.some.inj (sourceRow.symm.trans found)
    subst sourceBody
    obtain ⟨builder, builderRow, rfl⟩ := row found
    exact certificate.edges source builder builderRow target successor value imported

theorem BuilderAvailable.of_ext {before after : LS} {beforeImports afterImports : ImportedValues}
    (extension : before.Ext after)
    (preserved : ∀ block, block < before.blocks.size → afterImports block = beforeImports block)
    {block value : Nat} (available : BuilderAvailable before beforeImports block value) :
    BuilderAvailable after afterImports block value := by
  obtain ⟨body, row, available⟩ := available
  obtain ⟨next, nextRow, params, extra, append⟩ := extension.2 block body row
  refine ⟨next, nextRow, ?_⟩
  rcases available with imported | defined
  · exact Or.inl (preserved block (Array.getElem?_eq_some_iff.mp row).1 ▸ imported)
  · apply Or.inr
    simp only [cfgBlock, GIR.Block.defs] at defined ⊢
    rw [params, append, List.filterMap_append, ← List.append_assoc]
    exact List.mem_append_left _ defined

theorem LocalDefinitionBefore.available {body : GIR.Block} {value index : Nat}
    (before : LocalDefinitionBefore body value index) : value ∈ body.defs := by
  rcases before with parameter | ⟨prior, op, _, instruction⟩
  · exact List.mem_append_left _ parameter
  · apply List.mem_append_right
    exact List.mem_filterMap.mpr ⟨.def value op, List.mem_of_getElem? instruction, rfl⟩

theorem BuilderBefore.available {state : LS} {imports : ImportedValues}
    {block value index : Nat} (before : BuilderBefore state imports block value index) :
    BuilderAvailable state imports block value := by
  obtain ⟨body, row, before⟩ := before
  exact ⟨body, row, before.imp_right LocalDefinitionBefore.available⟩

theorem BuilderAvailable.before_end {state : LS} {imports : ImportedValues}
    {block value : Nat} (available : BuilderAvailable state imports block value) :
    ∃ body, state.blocks[block]? = some body ∧
      (value ∈ imports block ∨ LocalDefinitionBefore (cfgBlock body) value body.insts.size) := by
  obtain ⟨body, row, available⟩ := available
  refine ⟨body, row, ?_⟩
  rcases available with imported | defined
  · exact Or.inl imported
  · apply Or.inr
    rcases List.mem_append.mp defined with parameter | instruction
    · exact Or.inl parameter
    · obtain ⟨inst, member, result⟩ := List.mem_filterMap.mp instruction
      cases inst with
      | eff effect => cases result
      | term term => cases result
      | «def» result op =>
        simp only [Option.some.injEq] at result
        subst result
        obtain ⟨index, bound, found⟩ := List.mem_iff_getElem.mp member
        refine Or.inr ⟨index, op, ?_, ?_⟩
        · simpa only [cfgBlock, Array.length_toList] using bound
        · exact List.getElem?_eq_getElem bound |>.trans (congrArg some found)

theorem BuilderImportedSSA.initState : BuilderImportedSSA initState (fun _ => []) := by
  constructor
  · rfl
  · intro block body row
    simp [Goose.Lower.initState] at row
  · intro block body row
    simp [Goose.Lower.initState] at row
  · intro block body row
    simp [Goose.Lower.initState] at row

end Goose.Lower.Validation
