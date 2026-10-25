import Goose.Lower.Validation.ReplacementScopedOperandsFunctions
import Goose.GIR.ReplacementContentFlowProofsScopedIncomingSites

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR Goose.GIR.ReplacementContentFlow.Model

theorem scoped_entry_parameters_before {before finalState : LS} {func : Func}
    (initialDense : before.DenseDefinitions) (extension : before.Ext finalState)
    (blocks : func.blocks = finishBlocks finalState.blocks) (entryExists : 0 < before.blocks.size)
    {entry : GIR.Block} (entryAt : func.blocks[0]? = some entry)
    {value : ValueId} (parameter : value ∈ entry.params.map Prod.fst) : value < before.vals.size := by
  let initial := before.blocks[0]
  have initialAt : before.blocks[0]? = some initial := by simp [initial,entryExists]
  obtain ⟨next,nextAt,params,tail,append⟩ := extension.2 0 initial initialAt
  have entryEq : (⟨next.params,next.insts.toList⟩ : GIR.Block) = entry := by
    rw [blocks,finishBlocks,Array.getElem?_map,nextAt] at entryAt
    exact Option.some.inj entryAt
  rw [← entryEq] at parameter
  change value ∈ next.params.map Prod.fst at parameter
  rw [params] at parameter
  have inDefs : value ∈ before.defs := by
    apply List.mem_flatMap.mpr
    refine ⟨initial,Array.mem_toList_iff.mpr (Array.mem_of_getElem? initialAt),?_⟩
    exact List.mem_append_left _ parameter
  exact List.mem_range.mp (initialDense.subset inDefs)

theorem lowerExpr_scoped_incoming_values (expression : Expr) {env before result captured finalState}
    (run : lowerExpr expression env before = (result,captured))
    (initialDense : before.DenseDefinitions) (initialLive : LiveBound before)
    (initialOperands : OperandBounds before) (initialTargets : TargetsBounded before)
    (finalDense : finalState.DenseDefinitions) (extension : captured.Ext finalState)
    (framed : IntervalEdgesFramed before captured finalState)
    {func : Func} (blocks : func.blocks = finishBlocks finalState.blocks)
    {value source : ValueId} (lower : before.vals.size ≤ value) (upper : value < captured.vals.size)
    (incoming : source ∈ allIncomingValues func value) :
    before.vals.size ≤ source ∧ source < captured.vals.size := by
  obtain ⟨block,term,target,args,receiver,parameter,member,termMember,edge,targetAt,pair,same⟩ :=
    allIncomingValues_site incoming
  obtain ⟨parameterValue,type⟩ := parameter
  change parameterValue = value at same
  subst parameterValue
  obtain ⟨position,parameterAt⟩ := List.mem_iff_getElem?.mp (List.of_mem_zip pair).1
  exact lowerExpr_scoped_incoming_operands expression run initialDense initialLive initialOperands initialTargets
    finalDense extension framed blocks targetAt parameterAt lower upper member termMember
    (termEdges_successor edge) source (termEdges_argument_used edge (List.of_mem_zip pair).2)

theorem lowerExpr_scoped_graph_inputs (expression : Expr) {env before result captured finalState}
    (run : lowerExpr expression env before = (result,captured))
    (initialDense : before.DenseDefinitions) (initialLive : LiveBound before)
    (initialOperands : OperandBounds before) (initialTargets : TargetsBounded before)
    (entryExists : 0 < before.blocks.size)
    (finalDense : finalState.DenseDefinitions) (extension : captured.Ext finalState)
    (framed : IntervalEdgesFramed before captured finalState)
    {func : Func} (blocks : func.blocks = finishBlocks finalState.blocks) :
    (∀ entry, func.blocks[0]? = some entry → ∀ value ∈ entry.params.map Prod.fst, value < before.vals.size) ∧
    (∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
      before.vals.size ≤ value → value < captured.vals.size →
        ∀ source ∈ (Inst.def value op).uses, before.vals.size ≤ source ∧ source < captured.vals.size) ∧
    (∀ value, before.vals.size ≤ value → value < captured.vals.size →
      ∀ source ∈ allIncomingValues func value, before.vals.size ≤ source ∧ source < captured.vals.size) := by
  refine ⟨?_,?_,?_⟩
  · intro entry entryAt value member
    exact scoped_entry_parameters_before initialDense
      ((lowerExpr_emitsFreshUses expression run).extension.trans extension) blocks entryExists entryAt member
  · intro block member value op defined lower upper
    exact lowerExpr_scoped_definition_operands expression run initialDense initialLive initialOperands
      finalDense extension blocks member defined lower upper
  · intro value lower upper source incoming
    exact lowerExpr_scoped_incoming_values expression run initialDense initialLive initialOperands initialTargets
      finalDense extension framed blocks lower upper incoming

#print axioms scoped_entry_parameters_before
#print axioms lowerExpr_scoped_incoming_values
#print axioms lowerExpr_scoped_graph_inputs

end Goose.Lower.Validation.ReplacementContentFlowSource
