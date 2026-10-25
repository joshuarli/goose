import Goose.Lower.Validation.SummaryPreservationEffectRefinement
import Goose.Lower.Validation.SummaryPreservationCallArguments
import Goose.Lower.Validation.SummaryPreservationCallTargets

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem expandedArgumentTargets_refines {func : Func} {actual source : List RootRef}
    (closed : ParameterRootsClosed func) (refined : RootsRefine func actual source) :
    ∀ target ∈ func.storageTargets (rootsTargets ((actual.flatMap func.expandParameterRoot).foldl
      (fun acc root => unionRoots acc [root]) [])),
      target ∈ func.storageTargets (rootsTargets source) := by
  intro target member
  exact refined.targets closed target (storageTargets_idempotent closed target
    (storageTargets_mono (expandedArgumentTargets_below func actual) target member))

theorem expandedCallArguments_storage_refines {func : Func} {provenance : Prov}
    {args : List ValueId} {sourceArgs : List (List RootRef)}
    (closed : ParameterRootsClosed func)
    (arguments : ∀ (index : Nat) (value : ValueId), args[index]? = some value →
      ∃ sourceRoots, sourceArgs[index]? = some sourceRoots ∧
        RootsRefine func (rootsAt provenance.vals value) sourceRoots) :
    ∀ (index : Nat) (target : Target),
      target ∈ func.storageTargets (rootsTargets ((args.map fun value =>
        ((rootsAt provenance.vals value).flatMap func.expandParameterRoot).foldl
          (fun acc root => unionRoots acc [root]) [])[index]?.getD [])) →
      target ∈ func.storageTargets (rootsTargets (sourceArgs[index]?.getD [])) := by
  intro index target member
  cases lookup : args[index]? with
  | none => simp [List.getElem?_map, lookup, rootsTargets, Func.storageTargets] at member
  | some value =>
    obtain ⟨sourceRoots, sourceLookup, refined⟩ := arguments index value lookup
    simp only [List.getElem?_map, lookup, Option.map_some, Option.getD_some] at member
    rw [sourceLookup]
    exact expandedArgumentTargets_refines closed refined target member

theorem mapSummaryTargets_storage_refines {func : Func} {actual source : List (List RootRef)}
    (arguments : ∀ (index : Nat) (target : Target),
      target ∈ func.storageTargets (rootsTargets (actual[index]?.getD [])) →
        target ∈ func.storageTargets (rootsTargets (source[index]?.getD []))) (targets : List Target) :
    ∀ target ∈ func.storageTargets (mapSummaryTargets actual targets),
      target ∈ func.storageTargets (mapSummaryTargets source targets) := by
  induction targets with
  | nil => simp [mapSummaryTargets, Func.storageTargets]
  | cons head rest ih =>
    intro target member
    cases head with
    | global global =>
      change target ∈ [.global global] ++ func.storageTargets (mapSummaryTargets actual rest) at member
      change target ∈ [.global global] ++ func.storageTargets (mapSummaryTargets source rest)
      rcases List.mem_append.mp member with same | prior
      · exact List.mem_append.mpr (Or.inl same)
      · exact List.mem_append.mpr (Or.inr (ih target prior))
    | param index =>
      rw [mapSummaryTargets, storageTargets_append] at member ⊢
      rcases List.mem_append.mp member with argument | prior
      · exact List.mem_append.mpr (Or.inl (arguments index target argument))
      · exact List.mem_append.mpr (Or.inr (ih target prior))

theorem mapCallTargets_storage_refines {func : Func} {callee : Impl} {ctx : Context}
    {actual source : List (List RootRef)}
    (arguments : ∀ (index : Nat) (target : Target),
      target ∈ func.storageTargets (rootsTargets (actual[index]?.getD [])) →
        target ∈ func.storageTargets (rootsTargets (source[index]?.getD []))) (targets : List Target) :
    ∀ target ∈ func.storageTargets (addTargets (mapSummaryTargets actual targets)
      (targets.flatMap fun | .param index => paramGlobals callee ctx index | .global _ => [])),
      target ∈ func.storageTargets (mapCallTargets callee ctx source targets) := by
  intro target member
  rcases storageTargets_addTargets_origin member with actualMember | globals
  · exact storageTargets_mono (mapSummaryTargets_in_call targets) target
      (mapSummaryTargets_storage_refines arguments targets target actualMember)
  · exact storageTargets_mono (callGlobals_in_call targets) target globals

end Goose.Lower.Validation.SummaryPreservation
