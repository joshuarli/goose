import Goose.Lower.Validation.ReplacementSourceSitesEvidence
import Goose.Lower.Validation.OperandBounds
import Goose.Lower.Validation.ReplacementScopedSourceFacts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceSites
import Goose.Lower.Validation.OperandFunctions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem instruction_in_finished {before after : LS} {func : Func}
    (extension : before.Ext after) (blocks : func.blocks = finishBlocks after.blocks)
    {inst : Inst} (member : inst ∈ before.insts) :
    ∃ block ∈ func.blocks.toList, inst ∈ block.insts := by
  obtain ⟨body, bodyMember, present⟩ := List.mem_flatMap.mp member
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp bodyMember)
  obtain ⟨next, nextAt, _, tail, appended⟩ := extension.2 index body row
  refine ⟨cfgBlock next, ?_, ?_⟩
  · rw [blocks, finishBlocks, Array.toList_map]
    exact List.mem_map.mpr ⟨next, Array.mem_toList_iff.mpr (Array.mem_of_getElem? nextAt), rfl⟩
  · change inst ∈ next.insts.toList
    rw [appended]
    exact List.mem_append_left _ present

theorem AcceptedReplacementSite.cleared_operandBounds {le : LEnv} {state : LS}
    {owner value : ValueId} {origin : OriginId}
    (site : AcceptedReplacementSite le state owner value origin)
    {func : Func} (blocks : func.blocks = finishBlocks state.blocks)
    (uses : ∀ inst ∈ site.site.cleared.insts, ∀ input ∈ inst.uses,
      input < site.site.cleared.vals.size)
    (ordered : ∀ block ∈ func.blocks.toList, ∀ result op,
      Inst.def result op ∈ block.insts → ∀ input ∈ op.uses, input < result) :
    OperandBounds site.site.cleared := by
  refine ⟨uses, ?_⟩
  intro result op present input used
  have extension : site.site.cleared.Ext state :=
    (advB_lowerExpr site.rhs _ _ _ _ site.site.rhsRun).ext.trans site.captured_extension
  obtain ⟨block, member, defined⟩ := instruction_in_finished extension blocks present
  exact ordered block member result op defined input used

theorem AcceptedReplacementSite.scoped_graph_inputs {le : LEnv} {state : LS}
    {owner value : ValueId} {origin : OriginId}
    (site : AcceptedReplacementSite le state owner value origin)
    {func : Func} (blocks : func.blocks = finishBlocks state.blocks)
    (uses : ∀ inst ∈ site.site.cleared.insts, ∀ input ∈ inst.uses,
      input < site.site.cleared.vals.size)
    (ordered : ∀ block ∈ func.blocks.toList, ∀ result op,
      Inst.def result op ∈ block.insts → ∀ input ∈ op.uses, input < result)
    (dense : state.DenseDefinitions) :
    (∀ entry, func.blocks[0]? = some entry →
      ∀ input ∈ entry.params.map Prod.fst, input < site.site.cleared.vals.size) ∧
    (∀ block ∈ func.blocks.toList, ∀ result op, Inst.def result op ∈ block.insts →
      site.site.cleared.vals.size ≤ result → result < site.site.captured.vals.size →
        ∀ input ∈ (Inst.def result op).uses,
          site.site.cleared.vals.size ≤ input ∧ input < site.site.captured.vals.size) ∧
    (∀ result, site.site.cleared.vals.size ≤ result → result < site.site.captured.vals.size →
      ∀ input ∈ ReplacementContentFlow.Model.allIncomingValues func result,
        site.site.cleared.vals.size ≤ input ∧ input < site.site.captured.vals.size) := by
  have entryExists : 0 < site.site.cleared.blocks.size := by
    have live := (dead_lowerExpr site.rhs).live_before site.site.rhsRun site.live
    cases current : site.site.cleared.cur with
    | none => simp [current] at live
    | some block => exact Nat.zero_lt_of_lt (site.cleared_generated.live block current)
  exact ReplacementContentFlowSource.lowerExpr_scoped_graph_inputs site.rhs site.site.rhsRun
    site.cleared_generated.dense site.cleared_generated.live
    (site.cleared_operandBounds blocks uses ordered) site.cleared_generated.targets entryExists
    dense site.captured_extension site.framed blocks

theorem ReplacementContentFlowSource.SiteOccurrences.cleared_operandBounds
    {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    {block position owner value : Nat} {origin : OriginId}
    (site : ReplacementContentFlowSource.SiteOccurrences env root targets le state func types upper
      block position owner value origin)
    (blocks : func.blocks = finishBlocks state.blocks)
    (ordered : ∀ body ∈ func.blocks.toList, ∀ result op,
      Inst.def result op ∈ body.insts → ∀ input ∈ op.uses, input < result) :
    OperandBounds site.source.site.source.site.cleared :=
  site.source.site.source.cleared_operandBounds blocks site.clearedOperandUses ordered

theorem ReplacementContentFlowSource.SiteOccurrences.context_cleared_operandBounds
    {module : Core.Module} {context : Context} {impl : Impl}
    {env : PEnv} {root : DemandNode} {targets : List BlockId} {le : LEnv}
    {types : Array (Option VTy)} {upper : Prov}
    {block position owner value : Nat} {origin : OriginId}
    (site : ReplacementContentFlowSource.SiteOccurrences env root targets le
      (cfg_implState module impl) (lowerContextAt module context impl) types upper
      block position owner value origin) :
    OperandBounds site.source.site.source.site.cleared :=
  site.cleared_operandBounds (cfg_context_blocks module context impl)
    (lowerContextAt_operand_bounds module context impl).2

theorem ReplacementContentFlowSource.SiteOccurrences.global_cleared_operandBounds
    {module : Core.Module} {global : Core.Global}
    {env : PEnv} {root : DemandNode} {targets : List BlockId} {le : LEnv}
    {types : Array (Option VTy)} {upper : Prov}
    {block position owner value : Nat} {origin : OriginId}
    (site : ReplacementContentFlowSource.SiteOccurrences env root targets le
      (cfg_globalState module global) (lowerGlobal module global).init types upper
      block position owner value origin) :
    OperandBounds site.source.site.source.site.cleared :=
  site.cleared_operandBounds (cfg_global_blocks module global)
    (lowerGlobal_operand_bounds module global).2

#print axioms AcceptedReplacementSite.cleared_operandBounds
#print axioms AcceptedReplacementSite.scoped_graph_inputs
#print axioms ReplacementContentFlowSource.SiteOccurrences.cleared_operandBounds
#print axioms ReplacementContentFlowSource.SiteOccurrences.context_cleared_operandBounds
#print axioms ReplacementContentFlowSource.SiteOccurrences.global_cleared_operandBounds

end Goose.Lower.Validation
