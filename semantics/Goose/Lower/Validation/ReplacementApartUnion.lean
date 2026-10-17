import Goose.Lower.Validation.ReplacementIndependence

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ReplacementApart.flatten {queries : ReplacementQueries} {owner : ValueId}
    {rows : List (List RootRef)}
    (apart : ∀ row ∈ rows, ReplacementApart queries owner (some row)) :
    ReplacementApart queries owner (some rows.flatten) := by
  cases ownerAt : queries.value owner with
  | none =>
    apply Or.inl
    congr 1
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro root member
    obtain ⟨row, rowMember, rootMember⟩ := List.mem_flatten.mp member
    rcases apart row rowMember with empty | empty | ⟨actual, ownerRoots, _, found, _⟩
    · have same := Option.some.inj empty
      subst row
      exact List.not_mem_nil rootMember
    · simp [ownerAt] at empty
    · simp [ownerAt] at found
  | some ownerRoots =>
    by_cases empty : ownerRoots = []
    · exact Or.inr (Or.inl (by simpa [empty] using ownerAt))
    · apply Or.inr ∘ Or.inr
      refine ⟨rows.flatten, ownerRoots, rfl, ownerAt, ?_⟩
      intro root member ownerRoot ownerMember
      obtain ⟨row, rowMember, rootMember⟩ := List.mem_flatten.mp member
      rcases apart row rowMember with rowEmpty | ownerEmpty | ⟨actual, actualOwner, actualAt, found, disjoint⟩
      · have same := Option.some.inj rowEmpty
        subst row
        exact False.elim (List.not_mem_nil rootMember)
      · exact False.elim (empty (Option.some.inj (ownerAt.symm.trans ownerEmpty)))
      · have same := Option.some.inj actualAt
        have sameOwner := Option.some.inj (found.symm.trans ownerAt)
        subst actual
        subst actualOwner
        exact disjoint root rootMember ownerRoot ownerMember

theorem ReplacementApart.of_flatten_subset {queries : ReplacementQueries} {owner : ValueId}
    {rows : List (List RootRef)} {roots : List RootRef}
    (apart : ∀ row ∈ rows, ReplacementApart queries owner (some row))
    (included : roots ⊆ rows.flatten) :
    ReplacementApart queries owner (some roots) :=
  (ReplacementApart.flatten apart).of_subset rfl included

#print axioms ReplacementApart.flatten
#print axioms ReplacementApart.of_flatten_subset

end Goose.Lower.Validation
