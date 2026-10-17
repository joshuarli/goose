import Goose.Lower.Validation.ReplacementContentFlowSourceRoots

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

private theorem mapResultRoots_known (args : List (List RootRef)) (roots : List RootRef)
    (known : ∀ root ∈ roots, ∃ actual, mapCalleeRoots args root = .ok actual)
    (acc : List RootRef) : ∃ actual, mapResultRoots args acc roots = .ok actual := by
  induction roots generalizing acc with
  | nil => exact ⟨acc, rfl⟩
  | cons root rest ih =>
    obtain ⟨mapped, found⟩ := known root (by simp)
    obtain ⟨actual, completed⟩ := ih (fun item member => known item (by simp [member])) (unionRoots acc mapped)
    exact ⟨actual, by simp only [mapResultRoots, found, bind, Except.bind]; exact completed⟩

theorem mappedBound_from_source {func : Func} {state : State} {args : List ValueId}
    {actualArgs sourceArgs : List (List RootRef)} {declared sourceResult : List RootRef}
    (queried : args.mapM (fun value => normalize func (flowAt state.values value)) = some actualArgs)
    (arguments : ∀ (index : Nat) (sourceRoots : List RootRef), sourceArgs[index]? = some sourceRoots →
      ∃ actual, actualArgs[index]? = some actual ∧
        ∀ root ∈ actual, root ∈ sourceRoots.flatMap func.expandParameterRoot)
    (sourceMapping : mapResultRoots sourceArgs [] declared = .ok sourceResult) :
    ∃ actual, mappedBound func state args declared = some actual ∧
      ∀ root ∈ actual, root ∈ sourceResult.flatMap func.expandParameterRoot := by
  have mapped := (mapResultRoots_ok sourceArgs declared [] sourceResult sourceMapping).2
  obtain ⟨actual, completed⟩ := mapResultRoots_known actualArgs declared (by
    intro root member
    cases root with
    | «local» slot => exact False.elim (mapped (.local slot) member)
    | global global => exact ⟨[.global global], rfl⟩
    | param index =>
      obtain ⟨sourceRoots, sourceRow, sourceWithin⟩ := mapped (.param index) member
      obtain ⟨actual, actualRow, within⟩ := arguments index sourceRoots sourceRow
      exact ⟨actual, by simp [mapCalleeRoots, actualRow, pure, Except.pure]⟩) []
  refine ⟨actual, ?_, ?_⟩
  · simp [mappedBound, queried, completed, Except.toOption]
  · intro root member
    rcases mapResultRoots_sub actualArgs declared [] actual completed root member with impossible |
      ⟨declaredRoot, declaredMember, origin⟩
    · cases impossible
    · cases declaredRoot with
      | «local» slot => exact False.elim origin
      | global global =>
        have identity : root = .global global := origin
        subst root
        exact List.mem_flatMap.mpr ⟨.global global, mapped (.global global) declaredMember,
          by simp [Func.expandParameterRoot]⟩
      | param index =>
        obtain ⟨actualRoots, actualRow, rootMember⟩ := origin
        obtain ⟨sourceRoots, sourceRow, sourceWithin⟩ := mapped (.param index) declaredMember
        obtain ⟨corresponding, correspondingRow, within⟩ := arguments index sourceRoots sourceRow
        have same : corresponding = actualRoots := Option.some.inj (correspondingRow.symm.trans actualRow)
        subst corresponding
        obtain ⟨sourceRoot, sourceMember, expanded⟩ := List.mem_flatMap.mp (within root rootMember)
        exact List.mem_flatMap.mpr ⟨sourceRoot, sourceWithin sourceRoot sourceMember, expanded⟩

#print axioms mappedBound_from_source

end Goose.Lower.Validation.ReplacementContentFlowSource
