import Goose.Lower.Validation.CfgSourceDominanceSource
import Goose.Lower.Validation.CfgSourceDominanceFunctionBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ImportedState.dominatingUses {state : LS} {imports : ImportedValues}
    (checked : ImportedState state imports) (func : Func) (blocks : func.blocks = finishBlocks state.blocks) :
    DominatingUses func := by
  have certificate := checked.certificate.finished func blocks
  have dense := dense_finishBlocks checked.definitions blocks
  have unique : (func.blocks.toList.flatMap GIR.Block.defs).Nodup := dense.nodup_iff.mpr List.nodup_range
  have numValues : func.numValues = state.vals.size := by
    rw [Func.numValues_eq_definition_count, blocks, finishBlocks_defs]
    exact checked.definitions.length
  apply certificate.dominatingUses unique
  · intro value bound
    have defined : value ∈ func.blocks.toList.flatMap GIR.Block.defs :=
      dense.mem_iff.mpr (List.mem_range.mpr bound)
    obtain ⟨body, member, defined⟩ := List.mem_flatMap.mp defined
    obtain ⟨block, blockBound, same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    have row : func.blocks[block]? = some body := by simpa [same] using Array.getElem?_eq_getElem blockBound
    obtain ⟨position, site⟩ := definitionAt_of_block_def row defined
    exact ⟨block, position, site⟩
  · intro block bound inst index instruction value operand
    have row : func.blocks[block]? = some func.blocks[block] := Array.getElem?_eq_getElem bound
    have builderRow : ∃ body, state.blocks[block]? = some body ∧ cfgBlock body = func.blocks[block] := by
      simpa only [blocks, finishBlocks, Array.getElem?_map, Option.map_eq_some_iff, cfgBlock] using row
    obtain ⟨body, bodyRow, same⟩ := builderRow
    rw [numValues]
    rcases certificate.operands block bound inst index instruction value operand with imported | localBefore
    · exact checked.importsBounded block (Array.getElem?_eq_some_iff.mp bodyRow).1 value imported
    · apply checked.definitions.mem_lt
      apply List.mem_flatMap.mpr
      refine ⟨body, Array.mem_toList_iff.mpr (Array.mem_of_getElem? bodyRow), ?_⟩
      change value ∈ (cfgBlock body).defs
      rw [same]
      exact localBefore.available

theorem lowerImpl_dominatingUses (module : Core.Module) (impl : Impl) : DominatingUses (lowerImpl module impl) := by
  let continuation : List ValueId → B Unit := fun params => do
    let pre := (impl.params.toList.zip params).map fun (param, value) =>
      (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
    let value ← lowerBlock none pre false impl.body
    finishFunction impl value
  have source : ∀ params, SSARun none params (fun _ => []) (continuation params) := by
    intro params
    refine ((ssa_sourceBlock none impl.body _ false).weaken ?_).bind fun value => ssa_finishFunction impl value
    intro value member
    obtain ⟨entry, entryMember, equal⟩ := List.mem_map.mp member
    obtain ⟨pair, pairMember, same⟩ := List.mem_map.mp entryMember
    subst entry
    exact equal ▸ (List.of_mem_zip pairMember).2
  obtain ⟨imports, checked⟩ := ssa_function_start
    (impl.params.toList.map fun param => VTy.data (tyOfVar impl param.var)) continuation source
    (lowerEnv module impl.vars impl.results.toList)
  exact checked.dominatingUses (lowerImpl module impl) rfl

theorem lowerContextAt_dominatingUses (module : Core.Module) (context : Context) (impl : Impl) :
    DominatingUses (lowerContextAt module context impl) :=
  lowerImpl_dominatingUses module impl

theorem lowerGlobal_dominatingUses (module : Core.Module) (global : Core.Global) :
    DominatingUses (lowerGlobal module global).init := by
  let continuation : List ValueId → B Unit := fun _ => do
    let value ← lowerExpr global.init
    emitTerm (.ret [value] (some global.org))
  have source : ∀ params, SSARun none params (fun _ => []) (continuation params) := fun params =>
    ((ssa_sourceExpr none global.init).bind fun value =>
      ssa_emitTerm none (.ret [value] (some global.org)) (by simp [Term.successors])).weaken (by simp)
  obtain ⟨imports, checked⟩ := ssa_function_start [] continuation source (lowerEnv module #[] [global.ty])
  exact checked.dominatingUses (lowerGlobal module global).init rfl

theorem lowerImpl_cfgUseScan (module : Core.Module) (impl : Impl) (label : String) :
    cfgUseScan label (lowerImpl module impl) = .ok () :=
  dominatingUses_checked _ (lowerImpl_dominatingUses module impl) label

theorem lowerContextAt_cfgUseScan (module : Core.Module) (context : Context) (impl : Impl) (label : String) :
    cfgUseScan label (lowerContextAt module context impl) = .ok () :=
  dominatingUses_checked _ (lowerContextAt_dominatingUses module context impl) label

theorem lowerGlobal_cfgUseScan (module : Core.Module) (global : Core.Global) (label : String) :
    cfgUseScan label (lowerGlobal module global).init = .ok () :=
  dominatingUses_checked _ (lowerGlobal_dominatingUses module global) label

end Goose.Lower.Validation
