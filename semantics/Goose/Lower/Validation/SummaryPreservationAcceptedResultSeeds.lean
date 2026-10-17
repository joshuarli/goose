import Goose.Lower.Validation.SummaryPreservationAcceptedSummaries
import Goose.Lower.Validation.SummaryPreservationResultSeeds

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem accepted_resultRoots_seed_equivalent {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (index : Nat) (root : RootRef) :
    root ∈ rootsAt (resultRoots (lower module) (lower module).implTypes) index ↔
      root ∈ rootsAt (lower module).declaredResultRoots index := by
  rw [module_implTypes_eq_native]
  constructor
  · intro member
    have upper := accepted_resultRoots_below accepted index root member
    cases contextRow : module.contexts[index]? with
    | none => simp [rootsAt, moduleTypedResultUpper, Array.getElem?_map, contextRow] at upper
    | some ctx =>
      obtain ⟨impl, implementationRow, _⟩ := (validate_modOk module accepted).ctx index ctx contextRow
      have functionRow := lower_func_at contextRow implementationRow
      have implementation := (validate_modOk module accepted).impl ctx.impl impl implementationRow
      obtain ⟨bodyType, counter, typedBody, shape⟩ := implementation.body
      rcases shape with ⟨results, _⟩ | ⟨type, results, _⟩
      · have resultAt : impl.results[0]? = none := by rw [← Array.getElem?_toList, results]; rfl
        simp [rootsAt, moduleTypedResultUpper, Array.getElem?_map, contextRow,
          contextTypedResultUpper, implementationRow, resultAt] at upper
      · have resultAt : impl.results[0]? = some type := by rw [← Array.getElem?_toList, results]; rfl
        by_cases reference : type.isRefLike = true
        · have declared := accepted_resultRoots_declared accepted contextRow implementationRow root member
          have nativeResults : (lowerContextAt module ctx impl).results = [type] := by
            change impl.results.toList = [type]
            exact results
          have present : (lowerContextAt module ctx impl).roots.slots.isSome = true := rfl
          simpa only [rootsAt, Module.declaredResultRoots, Array.getElem?_map, functionRow,
            Option.map_some, Option.getD_some, nativeResults, present, Bool.true_and, reference,
            ite_true] using declared
        · simp [rootsAt, moduleTypedResultUpper, Array.getElem?_map, contextRow,
            contextTypedResultUpper, implementationRow, resultAt, reference] at upper
  · exact resultRoots_retains_declared (by simp) index root

#print axioms accepted_resultRoots_seed_equivalent

end Goose.Lower.Validation.SummaryPreservation
