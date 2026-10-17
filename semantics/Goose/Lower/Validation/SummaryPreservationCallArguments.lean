import Goose.Lower.Validation.SummaryPreservationCallEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem expandedCallArguments_storage_below {func : Func} {provenance : Prov}
    {args : List ValueId} {sourceArgs : List (List RootRef)}
    (closed : ParameterRootsClosed func)
    (arguments : ∀ (index : Nat) (value : ValueId), args[index]? = some value →
      ∃ sourceRoots, sourceArgs[index]? = some sourceRoots ∧
        RootsRepresent func (rootsAt provenance.vals value) sourceRoots) :
    ∀ (index : Nat) (target : Target),
      target ∈ func.storageTargets (rootsTargets ((args.map fun value =>
        ((rootsAt provenance.vals value).flatMap func.expandParameterRoot).foldl
          (fun acc root => unionRoots acc [root]) [])[index]?.getD [])) →
      target ∈ rootsTargets (sourceArgs[index]?.getD []) := by
  intro index target member
  cases lookup : args[index]? with
  | none =>
    simp [List.getElem?_map, lookup, rootsTargets, Func.storageTargets] at member
  | some value =>
    obtain ⟨sourceRoots, sourceLookup, represented⟩ := arguments index value lookup
    simp only [List.getElem?_map, lookup, Option.map_some, Option.getD_some] at member
    rw [sourceLookup]
    exact expandedArgumentTargets_represent closed represented target member

end Goose.Lower.Validation.SummaryPreservation
