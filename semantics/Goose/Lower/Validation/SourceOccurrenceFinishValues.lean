import Goose.GIR.AdmittedRegions
import Goose.Lower.Validation.SourceValueRecipeTypesAccepted
import Goose.Lower.Validation.SourceOccurrenceFinishContext
import Goose.Lower.Validation.SourceOccurrenceFinishGlobal
import Goose.Lower.Validation.SummaryPreservationReplayFinished
import Goose.Lower.Validation.SummaryPreservationFunctionSeeds

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem context_occurrence_provenance_values {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} {results : Array (List RootRef)}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (produced : ContextOccurrenceReplayProduced module ctx impl results) (rootCount : Nat) :
    ∀ row ∈ (lowerContextAt module ctx impl).roots.values.getD #[],
      rootsAt ((lowerContextAt module ctx impl).provenance results
        ((lowerContextAt module ctx impl).valueTypes (lower module)) rootCount).vals row.1 ⊆ row.2 := by
  obtain ⟨roots, range, after, upper, replayed, ready, returned, retained, ledger, sites⟩ := produced
  have below := ready.finished_provenance (cfg_context_blocks module ctx impl)
    (accepted_context_provenance_seed accepted contextRow implementationRow ready.slotsEq ready.recipes retained) rootCount
  intro row member root rootMember
  exact ready.recipes.valueRoots (lowerValueRootRows_covered _ _ _) row member
    (below.vals row.1 root rootMember)

theorem global_occurrence_provenance_values {module : Core.Module} {global : Core.Global}
    {results : Array (List RootRef)}
    (produced : GlobalOccurrenceReplayProduced module global results) (rootCount : Nat) :
    ∀ row ∈ (lowerGlobal module global).init.roots.values.getD #[],
      rootsAt ((lowerGlobal module global).init.provenance results
        ((lowerGlobal module global).init.valueTypes (lower module)) rootCount).vals row.1 ⊆ row.2 := by
  obtain ⟨roots, after, upper, replayed, ready, returned, ledger, sites⟩ := produced
  have below := ready.finished_provenance (cfg_global_blocks module global)
    (global_provenance_seed module global _ upper ready.recipes) rootCount
  intro row member root rootMember
  exact ready.recipes.valueRoots (lowerValueRootRows_covered _ _ _) row member
    (below.vals row.1 root rootMember)


theorem context_occurrence_admittedValues {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} {results : Array (List RootRef)}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (produced : ContextOccurrenceReplayProduced module ctx impl results) (rootCount : Nat) :
    (lowerContextAt module ctx impl).admittedValues
      ((lowerContextAt module ctx impl).valueTypes (lower module))
      ((lowerContextAt module ctx impl).provenance results
        ((lowerContextAt module ctx impl).valueTypes (lower module)) rootCount) = true := by
  apply List.all_eq_true.mpr
  intro row member
  have present := Array.mem_toList_iff.mp member
  apply Bool.and_eq_true_iff.mpr
  refine ⟨SourceValueRecipeTypes.lowerContextAt_valueRoots_refLike accepted implementationRow member, ?_⟩
  apply List.all_eq_true.mpr
  intro root rootMember
  exact List.contains_iff_mem.mpr
    (context_occurrence_provenance_values accepted contextRow implementationRow produced rootCount
      row present rootMember)

theorem global_occurrence_admittedValues {module : Core.Module} {global : Core.Global}
    {index : GlobalId} {results : Array (List RootRef)}
    (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global)
    (produced : GlobalOccurrenceReplayProduced module global results) (rootCount : Nat) :
    (lowerGlobal module global).init.admittedValues
      ((lowerGlobal module global).init.valueTypes (lower module))
      ((lowerGlobal module global).init.provenance results
        ((lowerGlobal module global).init.valueTypes (lower module)) rootCount) = true := by
  apply List.all_eq_true.mpr
  intro row member
  have present := Array.mem_toList_iff.mp member
  apply Bool.and_eq_true_iff.mpr
  refine ⟨SourceValueRecipeTypes.lowerGlobal_valueRoots_refLike accepted globalRow member, ?_⟩
  apply List.all_eq_true.mpr
  intro root rootMember
  exact List.contains_iff_mem.mpr
    (global_occurrence_provenance_values produced rootCount row present rootMember)

#print axioms context_occurrence_provenance_values
#print axioms global_occurrence_provenance_values
#print axioms context_occurrence_admittedValues
#print axioms global_occurrence_admittedValues

end Goose.Lower.Validation.ReplacementContentFlowSource
