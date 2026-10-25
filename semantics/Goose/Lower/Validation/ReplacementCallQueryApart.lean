import Goose.Lower.Validation.ReplacementApartUnion

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ReplacementApart.union {queries : ReplacementQueries} {owner : ValueId}
    {left right : List RootRef}
    (leftApart : ReplacementApart queries owner (some left))
    (rightApart : ReplacementApart queries owner (some right)) :
    ReplacementApart queries owner (some (unionRoots left right)) := by
  apply ReplacementApart.of_flatten_subset (rows := [left, right])
  · intro row member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same <;> subst row <;> assumption
  · intro root member
    rcases Core.Sound.unionRoots_mem _ _ _ member with leftAt | rightAt <;> simp [*]

theorem callDependencies_apart {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {owner function : ValueId} {arguments : List ValueId}
    (argumentApart : ∀ argument ∈ arguments, valRefLike types argument = true →
      ReplacementApart queries owner (queries.ownerDependencies argument))
    (calledApart : ReplacementApart queries owner (queries.callRoots function arguments))
    (declaredApart : ReplacementApart queries owner (callSummaryRoots module queries function arguments)) :
    ReplacementApart queries owner (callDependencies module types queries function arguments) := by
  by_cases ownerEmpty : queries.value owner = some []
  · exact Or.inr (Or.inl ownerEmpty)
  have extract : ∀ query, ReplacementApart queries owner query →
      ∃ roots, query = some roots ∧ ReplacementApart queries owner (some roots) := by
    intro query apart
    rcases apart with empty | empty | ⟨roots, ownerRoots, rootsAt, ownerAt, disjoint⟩
    · exact ⟨[], empty, Or.inl rfl⟩
    · exact False.elim (ownerEmpty empty)
    · exact ⟨roots, rootsAt, Or.inr (Or.inr ⟨roots, ownerRoots, rfl, ownerAt, disjoint⟩)⟩
  let step : List RootRef → ValueId → Option (List RootRef) := fun roots argument => do
    if !valRefLike types argument then pure roots else
      let actual ← queries.ownerDependencies argument
      pure (unionRoots roots actual)
  have accumulate : ∀ inputs : List ValueId, inputs ⊆ arguments → ∀ prior,
      ReplacementApart queries owner (some prior) →
      ∃ roots, inputs.foldlM step prior = some roots ∧ ReplacementApart queries owner (some roots) := by
    intro inputs
    induction inputs with
    | nil => intro _ prior apart; exact ⟨prior, rfl, apart⟩
    | cons argument rest ih =>
      intro included prior apart
      have tailBound : rest ⊆ arguments := fun {_} member => included (List.mem_cons_of_mem _ member)
      by_cases reference : valRefLike types argument = true
      · obtain ⟨actual, actualAt, actualApart⟩ := extract _
          (argumentApart argument (included (by simp)) reference)
        obtain ⟨roots, rootsAt, resultApart⟩ := ih tailBound _ (apart.union actualApart)
        exact ⟨roots, by simpa [List.foldlM_cons, step, reference, actualAt] using rootsAt, resultApart⟩
      · obtain ⟨roots, rootsAt, resultApart⟩ := ih tailBound prior apart
        exact ⟨roots, by simpa [List.foldlM_cons, step, reference] using rootsAt, resultApart⟩
  obtain ⟨inputs, inputsAt, inputsApart⟩ :=
    accumulate arguments (fun {_} member => member) [] (Or.inl rfl)
  obtain ⟨called, calledAt, calledApart⟩ := extract _ calledApart
  obtain ⟨declared, declaredAt, declaredApart⟩ := extract _ declaredApart
  have resultAt : callDependencies module types queries function arguments =
      some (unionRoots inputs (unionRoots called declared)) := by
    change ((arguments.foldlM step []).bind fun roots => do
      let actual ← queries.callRoots function arguments
      let touched ← callSummaryRoots module queries function arguments
      pure (unionRoots roots (unionRoots actual touched))) = _
    rw [inputsAt]
    simp [calledAt, declaredAt]
  rw [resultAt]
  exact inputsApart.union (calledApart.union declaredApart)

#print axioms callDependencies_apart

end Goose.Lower.Validation
