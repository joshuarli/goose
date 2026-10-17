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

theorem mappedBound_from_exact_source {func : Func} {state : State} {args : List ValueId}
    {actualArgs sourceArgs : List (List RootRef)} {declared sourceResult : List RootRef}
    (queried : args.mapM (fun value => normalize func (flowAt state.values value)) = some actualArgs)
    (arguments : ∀ (index : Nat) (sourceRoots : List RootRef), sourceArgs[index]? = some sourceRoots →
      ∃ actual, actualArgs[index]? = some actual ∧
        ∀ root, root ∈ actual ↔ root ∈ sourceRoots.flatMap func.expandParameterRoot)
    (sourceMapping : mapResultRoots sourceArgs [] declared = .ok sourceResult) :
    ∃ actual, mappedBound func state args declared = some actual ∧
      ∀ root, root ∈ actual ↔ root ∈ sourceResult.flatMap func.expandParameterRoot := by
  obtain ⟨actual, found, upper⟩ := mappedBound_from_source queried (by
    intro index sourceRoots row
    obtain ⟨roots, actualRow, exactRoots⟩ := arguments index sourceRoots row
    exact ⟨roots, actualRow, fun root member => (exactRoots root).mp member⟩) sourceMapping
  have actualMapping : mapResultRoots actualArgs [] declared = .ok actual := by
    cases mapped : mapResultRoots actualArgs [] declared with
    | error message => simp [mappedBound, queried, mapped, Except.toOption] at found
    | ok result =>
      have same : result = actual := by simpa [mappedBound, queried, mapped, Except.toOption] using found
      subst result
      rfl
  have mapped := (mapResultRoots_ok actualArgs declared [] actual actualMapping).2
  refine ⟨actual, found, fun root => ⟨upper root, ?_⟩⟩
  intro member
  obtain ⟨sourceRoot, sourceMember, expanded⟩ := List.mem_flatMap.mp member
  rcases mapResultRoots_sub sourceArgs declared [] sourceResult sourceMapping sourceRoot sourceMember with impossible |
      ⟨declaredRoot, declaredMember, origin⟩
  · cases impossible
  · cases declaredRoot with
    | «local» slot => exact False.elim origin
    | global global =>
      have identity : sourceRoot = .global global := origin
      subst sourceRoot
      have identity : root = .global global := by simpa [Func.expandParameterRoot] using expanded
      subst root
      exact mapped (.global global) declaredMember
    | param index =>
      obtain ⟨sourceRoots, sourceRow, rootMember⟩ := origin
      obtain ⟨actualRoots, actualRow, exactRoots⟩ := arguments index sourceRoots sourceRow
      have actualMember : root ∈ actualRoots := (exactRoots root).mpr
        (List.mem_flatMap.mpr ⟨sourceRoot, rootMember, expanded⟩)
      obtain ⟨mappedRoots, mappedRow, mappedWithin⟩ := mapped (.param index) declaredMember
      have same : mappedRoots = actualRoots := Option.some.inj (mappedRow.symm.trans actualRow)
      subst mappedRoots
      exact mappedWithin root actualMember

#print axioms mappedBound_from_exact_source

end Goose.Lower.Validation.ReplacementContentFlowSource
