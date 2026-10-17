import Goose.Lower.Validation.SummaryPreservationSourceFunction
import Goose.Lower.Validation.SummaryPreservationFunctionSeeds
import Goose.Lower.Validation.SummaryPreservationReplayFinished
import Goose.Lower.Validation.SummaryPreservationResults

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem accepted_context_returnedRoots_below {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} {candidate : Array (List RootRef)}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (bounded : RootsBelow candidate (moduleTypedResultUpper module)) (rootCount : Nat) :
    ∀ root ∈ (lowerContextAt module ctx impl).returnedRoots
      ((lowerContextAt module ctx impl).provenance candidate
        ((lowerContextAt module ctx impl).valueTypes (lower module)) rootCount),
      root ∈ contextTypedResultUpper module ctx := by
  obtain ⟨roots, range, after, upper, replayed, ready, returned, retained⟩ :=
    accepted_context_replay_produced accepted contextRow implementationRow bounded
  exact ready.finished_returnedRoots (cfg_context_blocks module ctx impl)
    (accepted_context_provenance_seed accepted implementationRow retained) returned rootCount

theorem accepted_resultRoots_below {module : Core.Module} (accepted : Core.validate module = .ok ()) :
    RootsBelow (resultRoots (lower module) ((lower module).funcs.map fun func => func.valueTypes (lower module)))
      (moduleTypedResultUpper module) := by
  apply resultRoots_below
  intro candidate bounded index func types paired
  obtain ⟨funcRow, typeRow⟩ := Array.getElem?_zip_eq_some.mp paired
  have bound : index < module.contexts.size := by
    simpa only [lower, Array.size_map] using (Array.getElem?_eq_some_iff.mp funcRow).1
  have contextRow := Array.getElem?_eq_getElem bound
  obtain ⟨impl, implementationRow, _⟩ := (validate_modOk module accepted).ctx index _ contextRow
  have same : func = lowerContextAt module module.contexts[index] impl :=
    Option.some.inj (funcRow.symm.trans (lower_func_at contextRow implementationRow))
  subst func
  have typeSame : types = (lowerContextAt module module.contexts[index] impl).valueTypes (lower module) := by
    simpa only [Array.getElem?_map, lower_func_at contextRow implementationRow, Option.map_some,
      Option.some.injEq] using typeRow.symm
  subst types
  intro root member
  have returned := accepted_context_returnedRoots_below accepted contextRow implementationRow bounded _ root member
  simpa only [rootsAt, moduleTypedResultUpper, Array.getElem?_map, contextRow, Option.map_some,
    Option.getD_some] using returned

theorem accepted_context_provenance_upper {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} {candidate : Array (List RootRef)}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (bounded : RootsBelow candidate (moduleTypedResultUpper module)) (rootCount : Nat) :
    ∃ upper, ProvenanceBelow ((lowerContextAt module ctx impl).provenance candidate
      ((lowerContextAt module ctx impl).valueTypes (lower module)) rootCount) upper ∧
      BuilderReturnsBound upper (contextTypedResultUpper module ctx) (cfg_implState module impl) := by
  obtain ⟨roots, range, after, upper, replayed, ready, returned, retained⟩ :=
    accepted_context_replay_produced accepted contextRow implementationRow bounded
  exact ⟨upper, ready.finished_provenance (cfg_context_blocks module ctx impl)
    (accepted_context_provenance_seed accepted implementationRow retained) rootCount, returned⟩

theorem accepted_context_computed_summaryClosed {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} {candidate : Array (List RootRef)}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (bounded : RootsBelow candidate (moduleTypedResultUpper module)) (rootCount : Nat) :
    (lowerContextAt module ctx impl).summaryClosed
      ((lowerContextAt module ctx impl).effects (lower module)
        ((lowerContextAt module ctx impl).provenance candidate
          ((lowerContextAt module ctx impl).valueTypes (lower module)) rootCount)) = .ok () := by
  obtain ⟨roots, range, after, upper, replayed, ready, returned, retained⟩ :=
    accepted_context_replay_produced accepted contextRow implementationRow bounded
  exact accepted_finished_summaryClosed accepted contextRow implementationRow replayed ready
    (cfg_context_blocks module ctx impl) rfl
    (accepted_context_provenance_seed accepted implementationRow retained) rootCount

theorem accepted_resultRoots_declared {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (root : RootRef)
    (member : root ∈ rootsAt (resultRoots (lower module)
      ((lower module).funcs.map fun func => func.valueTypes (lower module))) context) :
    root ∈ ((lowerContextAt module ctx impl).roots.results[0]?).getD [] := by
  have bounded := accepted_resultRoots_below accepted context root member
  simp only [rootsAt, moduleTypedResultUpper, Array.getElem?_map, contextRow, Option.map_some,
    Option.getD_some, contextTypedResultUpper, implementationRow] at bounded
  by_cases reference : (impl.results[0]?).any Ty.isRefLike = true
  · simp only [reference, ite_true] at bounded
    have resultBound : 0 < impl.results.size := by
      cases row : impl.results[0]? with
      | none => simp [row] at reference
      | some type => exact (Array.getElem?_eq_some_iff.mp row).1
    exact refinedResultUpper_lowerContext_result resultBound root (by
      simpa only [contextRefinedResultUpper, implementationRow] using bounded)
  · simp [reference] at bounded

#print axioms accepted_context_provenance_upper
#print axioms accepted_context_computed_summaryClosed
#print axioms accepted_resultRoots_declared

#print axioms accepted_context_returnedRoots_below
#print axioms accepted_resultRoots_below

end Goose.Lower.Validation.SummaryPreservation
