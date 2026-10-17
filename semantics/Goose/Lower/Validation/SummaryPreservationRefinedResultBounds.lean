import Goose.Lower.Validation.SummaryPreservationRefinedResults
import Goose.Lower.Validation.SummaryPreservationResults

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def contextRefinedResultUpper (module : Core.Module) (ctx : Context) : List RootRef :=
  match module.impls[ctx.impl]? with
  | none => []
  | some impl => refinedResultUpper (lowerContextAt module ctx impl)
      (ctx.resultRoots[0]?.getD [])

def moduleRefinedResultUpper (module : Core.Module) : Array (List RootRef) :=
  module.contexts.map (contextRefinedResultUpper module)

theorem moduleRefinedResultUpper_at {module : Core.Module} {index : ContextId} {ctx : Context}
    {impl : Impl} (contextLookup : module.contexts[index]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl) :
    (moduleRefinedResultUpper module)[index]? = some
      (refinedResultUpper (lowerContextAt module ctx impl) (ctx.resultRoots[0]?.getD [])) := by
  simp [moduleRefinedResultUpper, Array.getElem?_map, contextLookup, contextRefinedResultUpper, implLookup]

theorem candidateResult_refines {module : Core.Module} {candidate : Array (List RootRef)}
    {index : ContextId} {ctx : Context} {impl : Impl}
    (bounded : RootsBelow candidate (moduleRefinedResultUpper module))
    (contextLookup : module.contexts[index]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl) :
    RootsRefine (lowerContextAt module ctx impl) (rootsAt candidate index)
      (ctx.resultRoots[0]?.getD []) := by
  intro root member
  apply refinedResultUpper_refines (lowerContextAt module ctx impl) (ctx.resultRoots[0]?.getD []) root
  have upper := bounded index root member
  simpa only [rootsAt, moduleRefinedResultUpper_at contextLookup implLookup, Option.getD_some] using upper

end Goose.Lower.Validation.SummaryPreservation
