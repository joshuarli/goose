import Goose.Lower.Validation.SummaryPreservationTypedResultBounds

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem typedCandidateResult_default_nonref_empty {module : Core.Module}
    {candidate : Array (List RootRef)} {index : ContextId} {ctx : Context} {impl : Impl}
    (bounded : RootsBelow candidate (moduleTypedResultUpper module))
    (contextLookup : module.contexts[index]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl)
    (nonReference : ((impl.results[0]?).getD Ty.unit).isRefLike = false) :
    rootsAt candidate index = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro root member
  have upper := bounded index root member
  cases resultRow : impl.results[0]? with
  | none =>
    simp [rootsAt, moduleTypedResultUpper, Array.getElem?_map, contextLookup,
      contextTypedResultUpper, implLookup, resultRow] at upper
  | some ty =>
    simp only [resultRow, Option.getD_some] at nonReference
    simp [rootsAt, moduleTypedResultUpper, Array.getElem?_map, contextLookup,
      contextTypedResultUpper, implLookup, resultRow, nonReference] at upper

theorem rootsOfDef_call_default_nonref_empty {module : Core.Module}
    {candidate : Array (List RootRef)} {index : ContextId} {ctx : Context} {impl : Impl}
    (bounded : RootsBelow candidate (moduleTypedResultUpper module))
    (contextLookup : module.contexts[index]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl)
    (nonReference : ((impl.results[0]?).getD Ty.unit).isRefLike = false)
    (vt : Array (Option VTy)) (func : Func) (provenance : Prov) (result : ValueId)
    (args : List ValueId) (origin : Option OriginId) :
    rootsOfDef candidate vt func provenance result (.call index args origin) = [] := by
  simp only [rootsOfDef, typedCandidateResult_default_nonref_empty bounded contextLookup
    implLookup nonReference, List.flatMap_nil]

end Goose.Lower.Validation.SummaryPreservation
