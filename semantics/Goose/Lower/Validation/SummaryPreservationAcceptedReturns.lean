import Goose.Lower.Validation.SummaryPreservationAcceptedSummaries

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem accepted_function_return_roots_declared {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} {block : GIR.Block} {value : ValueId} {origin : Option OriginId}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (blockMember : block ∈ (lowerContextAt module ctx impl).blocks.toList)
    (returnMember : Inst.term (.ret [value] origin) ∈ block.insts) :
    ∀ root ∈ rootsAt ((lowerContextAt module ctx impl).provenance
      (resultRoots (lower module) (lower module).implTypes)
      ((lowerContextAt module ctx impl).valueTypes (lower module)) (lower module).rootCount).vals value,
      root ∈ ((lowerContextAt module ctx impl).roots.results[0]?).getD [] := by
  obtain ⟨roots, range, after, upper, replayed, ready, returned, retained⟩ :=
    accepted_context_replay_produced accepted contextRow implementationRow
      (accepted_resultRoots_implTypes_below accepted)
  have actual := ready.finished_provenance (cfg_context_blocks module ctx impl)
    (accepted_context_provenance_seed accepted contextRow implementationRow ready.slotsEq ready.recipes retained) (lower module).rootCount
  have instruction : Inst.term (.ret [value] origin) ∈ (cfg_implState module impl).insts :=
    finishBlocks_instruction_member (by simpa only [cfg_context_blocks] using blockMember) returnMember
  intro root member
  have bounded := returned value origin instruction root (actual.vals value root member)
  simp only [contextTypedResultUpper, implementationRow] at bounded
  by_cases reference : (impl.results[0]?).any Ty.isRefLike = true
  · simp only [reference, ite_true] at bounded
    have resultBound : 0 < impl.results.size := by
      cases row : impl.results[0]? with
      | none => simp [row] at reference
      | some type => exact (Array.getElem?_eq_some_iff.mp row).1
    exact refinedResultUpper_lowerContext_result resultBound root (by
      simpa only [contextRefinedResultUpper, implementationRow] using bounded)
  · simp [reference] at bounded

#print axioms accepted_function_return_roots_declared

end Goose.Lower.Validation.SummaryPreservation
