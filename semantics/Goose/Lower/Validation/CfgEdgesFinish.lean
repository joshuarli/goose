import Goose.Lower.Validation.CfgBuilderEdges
import Goose.Lower.Validation.CfgCheck
import Goose.Lower.Validation.CfgModuleStructure

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem EdgeArguments.finished {state : LS} {target : BlockId} {args : List ValueId}
    (edge : EdgeArguments state target args) (func : Func) (types : Array (Option VTy))
    (blocks : func.blocks = finishBlocks state.blocks) (retained : types = state.vals) :
    FuncEdgeArguments func types target args := by
  obtain ⟨body, row, arity, typed⟩ := edge
  refine ⟨⟨body.params, body.insts.toList⟩, ?_, arity, ?_⟩
  · simp [blocks, finishBlocks, Array.getElem?_map, row]
  · intro pair member
    rw [retained]
    exact typed pair member

theorem BuilderTermArguments.finished {state : LS} {term : Term}
    (edge : BuilderTermArguments state term) (func : Func) (types : Array (Option VTy))
    (blocks : func.blocks = finishBlocks state.blocks) (retained : types = state.vals) :
    TermArguments func types term := by
  cases term <;> try trivial
  case br target args => exact EdgeArguments.finished edge func types blocks retained
  case condbr condition yes yesArgs no noArgs =>
    exact ⟨EdgeArguments.finished edge.1 func types blocks retained,
      EdgeArguments.finished edge.2 func types blocks retained⟩

theorem BuilderEdgeArguments.finished {state : LS} (edges : BuilderEdgeArguments state)
    (func : Func) (types : Array (Option VTy))
    (blocks : func.blocks = finishBlocks state.blocks) (retained : types = state.vals) :
    ∀ block (bound : block < func.blocks.size) term,
      func.blocks[block].lastTerm? = some term → TermArguments func types term := by
  intro block bound term last
  have row : func.blocks[block]? = some func.blocks[block] := Array.getElem?_eq_getElem bound
  generalize actualEq : func.blocks[block] = actual at row last
  rw [blocks] at row
  simp only [finishBlocks, Array.getElem?_map, Option.map_eq_some_iff] at row
  obtain ⟨body, builderRow, same⟩ := row
  rw [← same] at last
  have final : body.insts.toList.getLast? = some (.term term) := by
    cases found : body.insts.toList.getLast? with
    | none => simp [GIR.Block.lastTerm?, found] at last
    | some inst =>
      cases inst with
      | «def» value op => simp [GIR.Block.lastTerm?, found] at last
      | eff effect => simp [GIR.Block.lastTerm?, found] at last
      | term actual =>
        have equality : actual = term := by simpa [GIR.Block.lastTerm?, found] using last
        simp only [equality]
  have typed := edges block body builderRow (.term term) (List.mem_of_getLast? final)
  exact BuilderTermArguments.finished typed func types blocks retained

theorem cfgFacts_of_builderEdges {state : LS} {func : Func} {types : Array (Option VTy)}
    (structureFacts : CfgStructure func) (edges : BuilderEdgeArguments state)
    (blocks : func.blocks = finishBlocks state.blocks) (retained : types = state.vals)
    (uses : DominatingUses func) : CfgFacts func types :=
  ⟨structureFacts.terminators, edges.finished func types blocks retained,
    structureFacts.entry, structureFacts.paths, uses⟩

theorem lowerImpl_checkCfg_of_builderEdges {module : Core.Module} {impl : Core.Impl} {state : LS}
    (edges : BuilderEdgeArguments state) (blocks : (lowerImpl module impl).blocks = finishBlocks state.blocks)
    (retained : (lowerImpl module impl).valueTypes (lower module) = state.vals)
    (uses : DominatingUses (lowerImpl module impl)) (label : String) :
    checkCfg label (lowerImpl module impl) ((lowerImpl module impl).valueTypes (lower module)) = .ok () :=
  cfgFacts_checked (cfgFacts_of_builderEdges (lowerImpl_cfgStructure module impl) edges blocks retained uses) label

end Goose.Lower.Validation
