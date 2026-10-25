import Goose.Lower.Validation.SummaryPreservationAcceptedResults

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem module_implTypes_eq_native (module : GIR.Module) :
    module.implTypes = module.funcs.map (fun func => func.valueTypes module) := by
  simp [GIR.Module.implTypes, GIR.Module.infos, GIR.Module.labelled, List.map_map, Function.comp_def]
  simp only [← Array.toList_map, Array.toArray_toList]

theorem accepted_resultRoots_implTypes_below {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    RootsBelow (resultRoots (lower module) (lower module).implTypes) (moduleTypedResultUpper module) := by
  rw [module_implTypes_eq_native]
  exact accepted_resultRoots_below accepted

theorem accepted_function_computed_summaryClosed {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl) :
    (lowerContextAt module ctx impl).summaryClosed
      ((lowerContextAt module ctx impl).effects (lower module)
        ((lowerContextAt module ctx impl).provenance
          (resultRoots (lower module) (lower module).implTypes)
          ((lowerContextAt module ctx impl).valueTypes (lower module)) (lower module).rootCount)) = .ok () :=
  accepted_context_computed_summaryClosed accepted contextRow implementationRow
    (accepted_resultRoots_implTypes_below accepted) _

#print axioms module_implTypes_eq_native
#print axioms accepted_resultRoots_implTypes_below
#print axioms accepted_function_computed_summaryClosed

end Goose.Lower.Validation.SummaryPreservation
