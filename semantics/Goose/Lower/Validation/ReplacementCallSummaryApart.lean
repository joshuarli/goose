import Goose.Lower.Validation.ReplacementCallQueryApart
import Goose.Lower.Validation.ReplacementCallEffectsApart

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem callSummaryRoots_known_apart {module : GIR.Module} {callee : Func}
    {queries : ReplacementQueries} {owner function : ValueId} {arguments : List ValueId}
    {summary : Core.Summary}
    (calleeAt : module.funcs[function]? = some callee) (summaryAt : callee.summary = .known summary)
    (argumentApart : ∀ argument ∈ arguments, ReplacementApart queries owner (queries.ownerDependencies argument))
    (globals : ∀ global, Target.global global ∈ summary.reads ++ summary.writes ++ summary.grows ++
      summary.shrinks ++ summary.rebinds → ReplacementApart queries owner (some [.global global]))
    (parameters : ∀ index, Target.param index ∈ summary.reads ++ summary.writes ++ summary.grows ++
      summary.shrinks ++ summary.rebinds →
      (∃ argument, arguments[index]? = some argument) ∧
        ReplacementApart queries owner (some ((((callee.roots.params.find? (·.1 == index)).map (·.2)).getD [])
          |>.filterMap fun | .global global => some (RootRef.global global) | _ => none))) :
    ReplacementApart queries owner (callSummaryRoots module queries function arguments) := by
  by_cases ownerEmpty : queries.value owner = some []
  · exact Or.inr (Or.inl ownerEmpty)
  have extract : ∀ query, ReplacementApart queries owner query →
      ∃ roots, query = some roots ∧ ReplacementApart queries owner (some roots) := by
    intro query apart
    rcases apart with empty | empty | ⟨roots, ownerRoots, rootsAt, ownerAt, disjoint⟩
    · exact ⟨[], empty, Or.inl rfl⟩
    · exact False.elim (ownerEmpty empty)
    · exact ⟨roots, rootsAt, Or.inr (Or.inr ⟨roots, ownerRoots, rfl, ownerAt, disjoint⟩)⟩
  let targets := summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks ++ summary.rebinds
  let step : List RootRef → Target → Option (List RootRef) := fun roots target => do
    match target with
    | .global global => pure (unionRoots roots [.global global])
    | .param index =>
      let argument ← arguments[index]?
      let actual ← queries.ownerDependencies argument
      let annotated := (((callee.roots.params.find? (·.1 == index)).map (·.2)).getD [])
        |>.filterMap fun | .global global => some (RootRef.global global) | _ => none
      pure (unionRoots roots (actual ++ annotated))
  have appendApart {left right : List RootRef}
      (leftApart : ReplacementApart queries owner (some left))
      (rightApart : ReplacementApart queries owner (some right)) :
      ReplacementApart queries owner (some (left ++ right)) := by
    apply ReplacementApart.of_flatten_subset (rows := [left, right])
    · intro row member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same <;> subst row <;> assumption
    · simp
  have accumulate : ∀ rest : List Target, rest ⊆ targets → ∀ prior,
      ReplacementApart queries owner (some prior) →
      ∃ roots, rest.foldlM step prior = some roots ∧ ReplacementApart queries owner (some roots) := by
    intro rest
    induction rest with
    | nil => intro _ prior apart; exact ⟨prior, rfl, apart⟩
    | cons target rest ih =>
      intro included prior apart
      have targetAt := included (by simp : target ∈ target :: rest)
      have restBound : rest ⊆ targets := fun {_} member => included (List.mem_cons_of_mem _ member)
      cases target with
      | global global =>
        obtain ⟨roots, rootsAt, resultApart⟩ := ih restBound _ (apart.union (globals global targetAt))
        exact ⟨roots, by simpa [List.foldlM_cons, step] using rootsAt, resultApart⟩
      | param index =>
        obtain ⟨⟨argument, argumentAt⟩, annotatedApart⟩ := parameters index targetAt
        obtain ⟨actual, actualAt, actualApart⟩ := extract _
          (argumentApart argument (List.mem_of_getElem? argumentAt))
        obtain ⟨roots, rootsAt, resultApart⟩ := ih restBound _ (apart.union (appendApart actualApart annotatedApart))
        exact ⟨roots, by simpa [List.foldlM_cons, step, argumentAt, actualAt] using rootsAt, resultApart⟩
  obtain ⟨roots, rootsAt, apart⟩ := accumulate targets (fun {_} member => member) [] (Or.inl rfl)
  have equal : callSummaryRoots module queries function arguments = targets.foldlM step [] := by
    unfold callSummaryRoots
    simp only [calleeAt, summaryAt]
    apply congrArg (fun operation => targets.foldlM operation [])
    funext prior target
    cases target with
    | global global => rfl
    | param index => dsimp only [step]; congr 4
  rw [equal, rootsAt]
  exact apart

#print axioms callSummaryRoots_known_apart

end Goose.Lower.Validation
