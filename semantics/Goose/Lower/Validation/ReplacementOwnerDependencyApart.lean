import Goose.Lower.Validation.ReplacementApartUnion
import Goose.GIR.ReplacementContentFlowProofsSliceDependencyAtoms

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR ReplacementContentFlow.Model

def OwnerDependencyApart (module : GIR.Module) (func : Func)
    (queries : ReplacementQueries) (owner : ValueId) (atom : Atom) : Prop :=
  ∃ roots, ownerDependencies module func (.known [atom]) = some roots ∧
    ReplacementApart queries owner (some roots)

theorem ownerDependencies_atoms_apart {module : GIR.Module} {func : Func}
    {queries : ReplacementQueries} {owner : ValueId} {raw : Roots} {roots : List RootRef}
    (known : ownerDependencies module func raw = some roots)
    (apart : ReplacementApart queries owner (some roots)) :
    raw.AtomsWithin (OwnerDependencyApart module func queries owner) := by
  cases raw with
  | pending => simp [ownerDependencies, rawOwnerTouches, Roots.bind, normalize] at known
  | unknown => simp [ownerDependencies, rawOwnerTouches, Roots.bind, normalize] at known
  | known rawAtoms =>
    intro atom member
    obtain ⟨actual, actualAt, included⟩ := ownerDependencies_atomsWithin known atom member
    exact ⟨actual, actualAt, apart.of_subset rfl included⟩

theorem ownerDependencies_apart_of_atoms {module : GIR.Module} {func : Func}
    {queries : ReplacementQueries} {owner : ValueId} {raw : Roots} {roots : List RootRef}
    (atoms : raw.AtomsWithin (OwnerDependencyApart module func queries owner))
    (known : ownerDependencies module func raw = some roots) :
    ReplacementApart queries owner (some roots) := by
  cases raw with
  | pending => simp [ownerDependencies, rawOwnerTouches, Roots.bind, normalize] at known
  | unknown => simp [ownerDependencies, rawOwnerTouches, Roots.bind, normalize] at known
  | known rawAtoms =>
    cases ownerAt : queries.value owner with
    | none =>
      have empty : (Roots.known rawAtoms).AtomsWithin (OwnerDependencyAtom module func []) := by
        intro atom member
        obtain ⟨actual, actualAt, apart⟩ := atoms atom member
        have actualEmpty : actual = [] := by
          rcases apart with empty | empty | ⟨_, _, _, found, _⟩
          · exact Option.some.inj empty
          · simp [ownerAt] at empty
          · simp [ownerAt] at found
        exact ⟨actual, actualAt, by simp [actualEmpty]⟩
      have within := ownerDependencies_within_of_atomsWithin empty known
      exact Or.inl (congrArg some (List.eq_nil_iff_forall_not_mem.mpr
        (fun root member => List.not_mem_nil (within member))))
    | some ownerRoots =>
      let separated := roots.filter fun root => ownerRoots.all fun target => !rootsMayOverlap root target
      have bounded : (Roots.known rawAtoms).AtomsWithin (OwnerDependencyAtom module func separated) := by
        intro atom member
        obtain ⟨actual, actualAt, apart⟩ := atoms atom member
        obtain ⟨upper, upperAt, upperBound⟩ := ownerDependencies_atomsWithin known atom member
        have same : upper = actual := Option.some.inj (upperAt.symm.trans actualAt)
        subst upper
        refine ⟨actual, actualAt, ?_⟩
        intro root rootAt
        apply List.mem_filter.mpr
        refine ⟨upperBound rootAt, ?_⟩
        apply List.all_eq_true.mpr
        intro target targetAt
        have disjoint : rootsMayOverlap root target = false := by
          rcases apart with empty | empty | ⟨foundRoots, foundOwner, foundAt, foundOwnerAt, disjoint⟩
          · have nil := Option.some.inj empty
            simp [nil] at rootAt
          · have nil : ownerRoots = [] := Option.some.inj (ownerAt.symm.trans empty)
            simp [nil] at targetAt
          · have sameRoots : foundRoots = actual := Option.some.inj foundAt.symm
            have sameOwner : foundOwner = ownerRoots := Option.some.inj (foundOwnerAt.symm.trans ownerAt)
            subst foundRoots
            subst foundOwner
            exact disjoint root rootAt target targetAt
        simp [disjoint]
      have included := ownerDependencies_within_of_atomsWithin bounded known
      refine Or.inr (Or.inr ⟨roots, ownerRoots, rfl, ownerAt, ?_⟩)
      intro root rootAt target targetAt
      have filtered := List.mem_filter.mp (included rootAt)
      have separatedAt := List.all_eq_true.mp filtered.2 target targetAt
      simpa using separatedAt

#print axioms ownerDependencies_atoms_apart
#print axioms ownerDependencies_apart_of_atoms

end Goose.Lower.Validation
