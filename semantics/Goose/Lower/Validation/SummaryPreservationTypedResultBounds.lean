import Goose.Lower.Validation.SummaryPreservationRefinedResultBounds

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def contextTypedResultUpper (module : Core.Module) (ctx : Context) : List RootRef :=
  match module.impls[ctx.impl]? with
  | none => []
  | some impl =>
    if (impl.results[0]?).any Ty.isRefLike then contextRefinedResultUpper module ctx else []

def moduleTypedResultUpper (module : Core.Module) : Array (List RootRef) :=
  module.contexts.map (contextTypedResultUpper module)


theorem typedResultUpper_below_refined (module : Core.Module) :
    RootsBelow (moduleTypedResultUpper module) (moduleRefinedResultUpper module) := by
  intro index root member
  cases contextRow : module.contexts[index]? with
  | none => simp [rootsAt, moduleTypedResultUpper, Array.getElem?_map, contextRow] at member
  | some ctx =>
    simp only [rootsAt, moduleTypedResultUpper, moduleRefinedResultUpper,
      Array.getElem?_map, contextRow, Option.map_some, Option.getD_some] at member ⊢
    unfold contextTypedResultUpper at member
    split at member
    · cases member
    · split at member
      · exact member
      · cases member


theorem typedCandidateResult_refines {module : Core.Module} {candidate : Array (List RootRef)}
    {index : ContextId} {ctx : Context} {impl : Impl}
    (bounded : RootsBelow candidate (moduleTypedResultUpper module))
    (contextLookup : module.contexts[index]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl) :
    RootsRefine (lowerContextAt module ctx impl) (rootsAt candidate index)
      (ctx.resultRoots[0]?.getD []) := by
  apply candidateResult_refines (contextLookup := contextLookup) (implLookup := implLookup)
  intro position root member
  exact typedResultUpper_below_refined module position root (bounded position root member)


theorem typedCandidateResult_nonref_empty {module : Core.Module} {candidate : Array (List RootRef)}
    {index : ContextId} {ctx : Context} {impl : Impl} {ty : Ty}
    (bounded : RootsBelow candidate (moduleTypedResultUpper module))
    (contextLookup : module.contexts[index]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl)
    (resultLookup : impl.results[0]? = some ty) (nonReference : ty.isRefLike = false) :
    rootsAt candidate index = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro root member
  have upper := bounded index root member
  simp [rootsAt, moduleTypedResultUpper, Array.getElem?_map, contextLookup,
    contextTypedResultUpper, implLookup, resultLookup, nonReference] at upper


theorem rootsOfDef_call_nonref_empty {module : Core.Module} {candidate : Array (List RootRef)}
    {index : ContextId} {ctx : Context} {impl : Impl} {ty : Ty}
    (bounded : RootsBelow candidate (moduleTypedResultUpper module))
    (contextLookup : module.contexts[index]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl)
    (resultLookup : impl.results[0]? = some ty) (nonReference : ty.isRefLike = false)
    (vt : Array (Option VTy)) (func : Func) (provenance : Prov) (result : ValueId)
    (args : List ValueId) (origin : Option OriginId) :
    rootsOfDef candidate vt func provenance result (.call index args origin) = [] := by
  simp only [rootsOfDef, typedCandidateResult_nonref_empty bounded contextLookup implLookup resultLookup
    nonReference, List.flatMap_nil]

end Goose.Lower.Validation.SummaryPreservation
