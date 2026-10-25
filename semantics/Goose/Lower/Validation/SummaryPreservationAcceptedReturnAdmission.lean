import Goose.GIR.AdmittedRegions
import Goose.Lower.Validation.SummaryPreservationAcceptedReturns
import Goose.Lower.Validation.SummaryPreservationAcceptedResultSeeds
import Goose.Lower.Validation.SummaryPreservationSourceReturnArity

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem accepted_function_admitted_singleton_return {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} {block : GIR.Block} {value : ValueId} {origin : Option OriginId}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (blockMember : block ∈ (lowerContextAt module ctx impl).blocks.toList)
    (returnMember : Inst.term (.ret [value] origin) ∈ block.insts) :
    (lowerContextAt module ctx impl).admittedInstruction (lower module)
      ((lowerContextAt module ctx impl).valueTypes (lower module))
      ((lowerContextAt module ctx impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module ctx impl).valueTypes (lower module)) (lower module).rootCount)
      (.term (.ret [value] origin)) = true := by
  have covered := accepted_function_return_roots_declared accepted contextRow implementationRow
    blockMember returnMember
  have all : (rootsAt ((lowerContextAt module ctx impl).provenance
      (resultRoots (lower module) (lower module).implTypes)
      ((lowerContextAt module ctx impl).valueTypes (lower module)) (lower module).rootCount).vals value).all
      (((lowerContextAt module ctx impl).roots.results[0]?).getD []).contains = true := by
    simpa only [List.all_eq_true, List.contains_iff_mem] using covered
  simp [Func.admittedInstruction, all]

theorem accepted_function_returnedRoots_closed {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl) :
    ∀ root ∈ (lowerContextAt module ctx impl).returnedRoots
      ((lowerContextAt module ctx impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module ctx impl).valueTypes (lower module)) (lower module).rootCount),
      root ∈ rootsAt (resultRoots (lower module) (lower module).implTypes) context := by
  intro root member
  have upper := accepted_context_returnedRoots_below accepted contextRow implementationRow
    (accepted_resultRoots_implTypes_below accepted) (lower module).rootCount root member
  apply (accepted_resultRoots_seed_equivalent accepted context root).mpr
  have implementation := (validate_modOk module accepted).impl ctx.impl impl implementationRow
  obtain ⟨bodyType, counter, typedBody, shape⟩ := implementation.body
  rcases shape with ⟨results, _⟩ | ⟨type, results, _⟩
  · have resultAt : impl.results[0]? = none := by rw [← Array.getElem?_toList, results]; rfl
    simp [contextTypedResultUpper, implementationRow, resultAt] at upper
  · have resultAt : impl.results[0]? = some type := by rw [← Array.getElem?_toList, results]; rfl
    by_cases reference : type.isRefLike = true
    · have bound : 0 < impl.results.size := (Array.getElem?_eq_some_iff.mp resultAt).1
      have declared := refinedResultUpper_lowerContext_result bound root (by
        simpa only [contextTypedResultUpper, implementationRow, resultAt, Option.any_some,
          reference, ite_true, contextRefinedResultUpper] using upper)
      have nativeResults : (lowerContextAt module ctx impl).results = [type] := results
      have present : (lowerContextAt module ctx impl).roots.slots.isSome = true := rfl
      simpa only [rootsAt, Module.declaredResultRoots, Array.getElem?_map,
        lower_func_at contextRow implementationRow, Option.map_some, Option.getD_some,
        nativeResults, present, Bool.true_and, reference, ite_true] using declared
    · simp [contextTypedResultUpper, implementationRow, resultAt, reference] at upper

#print axioms accepted_function_admitted_singleton_return
#print axioms accepted_function_returnedRoots_closed

theorem accepted_function_admitted_return {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} {block : GIR.Block} {values : List ValueId} {origin : Option OriginId}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (blockMember : block ∈ (lowerContextAt module ctx impl).blocks.toList)
    (returnMember : Inst.term (.ret values origin) ∈ block.insts) :
    (lowerContextAt module ctx impl).admittedInstruction (lower module)
      ((lowerContextAt module ctx impl).valueTypes (lower module))
      ((lowerContextAt module ctx impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module ctx impl).valueTypes (lower module)) (lower module).rootCount)
      (.term (.ret values origin)) = true := by
  have instruction : Inst.term (.ret values origin) ∈ (cfg_implState module impl).insts :=
    finishBlocks_instruction_member (by simpa only [cfg_context_blocks] using blockMember) returnMember
  have arity := SourceReturnArity.implementation_return_arity module impl values origin instruction
  cases values with
  | nil => rfl
  | cons value rest =>
    cases rest with
    | nil => exact accepted_function_admitted_singleton_return accepted contextRow implementationRow blockMember returnMember
    | cons second rest => simp at arity

#print axioms accepted_function_admitted_return

end Goose.Lower.Validation.SummaryPreservation
