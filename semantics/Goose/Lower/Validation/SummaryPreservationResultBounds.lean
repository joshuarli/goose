import Goose.Lower.Validation.SummaryPreservationRootBounds
import Goose.Lower.Validation.SummaryPreservationResults

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def contextResultUpper (module : Core.Module) (ctx : Context) : List RootRef :=
  match module.impls[ctx.impl]? with
  | none => []
  | some impl => allowedRoots (lowerContextAt module ctx impl)
      (ctx.resultRoots[0]?.getD [])

def moduleResultUpper (module : Core.Module) : Array (List RootRef) :=
  module.contexts.map (contextResultUpper module)

theorem moduleResultUpper_at {module : Core.Module} {index : ContextId} {ctx : Context}
    {impl : Impl} (contextLookup : module.contexts[index]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl) :
    (moduleResultUpper module)[index]? = some
      (allowedRoots (lowerContextAt module ctx impl) (ctx.resultRoots[0]?.getD [])) := by
  simp [moduleResultUpper, Array.getElem?_map, contextLookup, contextResultUpper, implLookup]

theorem candidateResult_represent {module : Core.Module} {candidate : Array (List RootRef)}
    {index : ContextId} {ctx : Context} {impl : Impl}
    (bounded : RootsBelow candidate (moduleResultUpper module))
    (contextLookup : module.contexts[index]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl) :
    RootsRepresent (lowerContextAt module ctx impl) (rootsAt candidate index)
      (ctx.resultRoots[0]?.getD []) := by
  intro root member
  apply allowedRoots_represent (lowerContextAt module ctx impl) (ctx.resultRoots[0]?.getD []) root
  have upper := bounded index root member
  simpa only [rootsAt, moduleResultUpper_at contextLookup implLookup, Option.getD_some] using upper

end Goose.Lower.Validation.SummaryPreservation
