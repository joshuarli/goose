import Goose.GIR.ReplacementContentFlow

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem normalizeAtom_ofRootRef (f : Func) (root : RootRef) :
    normalizeAtom f (Atom.ofRootRef root) = some (f.expandParameterRoot root) := by
  cases root <;> rfl

theorem normalize_rootMap (f : Func) (roots : List RootRef) :
    normalize f (.known (roots.map Atom.ofRootRef)) =
      some (roots.foldl (fun accumulated root => unionRoots accumulated (f.expandParameterRoot root)) []) := by
  simp only [normalize, List.foldlM_map, normalizeAtom_ofRootRef]
  exact List.foldlM_pure

theorem unionRoots_mem_iff (left right : List RootRef) (root : RootRef) :
    root ∈ unionRoots left right ↔ root ∈ left ∨ root ∈ right := by
  induction right generalizing left with
  | nil => simp [unionRoots]
  | cons head tail ih =>
      change root ∈ unionRoots (if left.contains head then left else left ++ [head]) tail ↔ _
      rw [ih]
      by_cases member : head ∈ left
      · have present : left.contains head = true := List.contains_iff_mem.mpr member
        simp only [present, ite_true, List.mem_cons]
        constructor
        · intro known
          rcases known with known | known
          · exact Or.inl known
          · exact Or.inr (Or.inr known)
        · intro known
          rcases known with known | equal | known
          · exact Or.inl known
          · subst root
            exact Or.inl member
          · exact Or.inr known
      · have absent : left.contains head = false := by
          apply Bool.eq_false_iff.mpr
          intro present
          exact member (List.contains_iff_mem.mp present)
        simp only [absent, Bool.false_eq_true, ite_false, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · intro known
          rcases known with (known | equal) | known
          · exact Or.inl known
          · exact Or.inr (Or.inl equal)
          · exact Or.inr (Or.inr known)
        · intro known
          rcases known with known | equal | known
          · exact Or.inl (Or.inl known)
          · exact Or.inl (Or.inr equal)
          · exact Or.inr known

theorem fold_expanded_roots_mem (f : Func) (roots accumulated : List RootRef) (root : RootRef) :
    root ∈ roots.foldl (fun current next => unionRoots current (f.expandParameterRoot next)) accumulated ↔
      root ∈ accumulated ∨ root ∈ roots.flatMap f.expandParameterRoot := by
  induction roots generalizing accumulated with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons, ih, unionRoots_mem_iff, List.flatMap_cons, List.mem_append]
      exact or_assoc

theorem normalize_rootMap_known (f : Func) (roots : List RootRef) :
    ∃ actual, normalize f (.known (roots.map Atom.ofRootRef)) = some actual ∧
      ∀ root, root ∈ actual ↔ root ∈ roots.flatMap f.expandParameterRoot := by
  refine ⟨_, normalize_rootMap f roots, ?_⟩
  intro root
  simpa only [List.not_mem_nil, false_or] using fold_expanded_roots_mem f roots [] root

theorem normalize_rootMap_dedup_known (f : Func) (roots : List RootRef) :
    ∃ actual, normalize f (.known (roots.eraseDups.map Atom.ofRootRef)) = some actual ∧
      ∀ root, root ∈ actual ↔ root ∈ roots.flatMap f.expandParameterRoot := by
  obtain ⟨actual, known, members⟩ := normalize_rootMap_known f roots.eraseDups
  refine ⟨actual, known, ?_⟩
  intro root
  rw [members]
  simp only [List.mem_flatMap, List.mem_eraseDups]

theorem normalize_fold_within (f : Func) (atoms : List Atom) (expected : List RootRef)
    (mapped : ∀ atom ∈ atoms, ∃ roots, normalizeAtom f atom = some roots ∧ roots ⊆ expected)
    (initial : List RootRef) (valid : initial ⊆ expected) :
    ∃ actual, atoms.foldlM (fun result root => do
      let next ← normalizeAtom f root
      pure (unionRoots result next)) initial = some actual ∧ actual ⊆ expected := by
  induction atoms generalizing initial with
  | nil => exact ⟨initial, rfl, valid⟩
  | cons atom rest ih =>
    obtain ⟨roots, known, within⟩ := mapped atom (by simp)
    obtain ⟨actual, result, included⟩ := ih
      (fun next member => mapped next (List.mem_cons_of_mem atom member))
      (unionRoots initial roots) (by
        intro root member
        rcases (unionRoots_mem_iff _ _ _).mp member with first | next
        · exact valid first
        · exact within next)
    exact ⟨actual, by simpa [List.foldlM_cons, known] using result, included⟩

theorem normalize_fold_atoms (f : Func) (atoms : List Atom) (initial actual : List RootRef)
    (known : atoms.foldlM (fun result root => do
      let next ← normalizeAtom f root
      pure (unionRoots result next)) initial = some actual) :
    initial ⊆ actual ∧ ∀ atom ∈ atoms,
      ∃ roots, normalizeAtom f atom = some roots ∧ roots ⊆ actual := by
  induction atoms generalizing initial with
  | nil => cases known; exact ⟨List.Subset.refl _, by simp⟩
  | cons atom rest ih =>
    cases nextAt : normalizeAtom f atom with
    | none => simp [List.foldlM_cons, nextAt] at known
    | some roots =>
      have remaining : rest.foldlM (fun result root => do
          let next ← normalizeAtom f root
          pure (unionRoots result next)) (unionRoots initial roots) = some actual := by
        simpa [List.foldlM_cons, nextAt] using known
      obtain ⟨included, mapped⟩ := ih _ remaining
      constructor
      · intro root member
        exact included ((unionRoots_mem_iff _ _ _).mpr (Or.inl member))
      · intro next member
        rcases List.mem_cons.mp member with equal | later
        · subst next
          exact ⟨roots, nextAt, fun root member => included ((unionRoots_mem_iff _ _ _).mpr (Or.inr member))⟩
        · exact mapped next later

theorem join_known_subset (left right : List Atom) :
    ∃ actual, (Roots.known left).join (.known right) = .known actual ∧ actual ⊆ left ++ right := by
  refine ⟨_, rfl, ?_⟩
  apply List.foldlRecOn (motive := fun current => current ⊆ left ++ right) right _
    (by intro root member; exact List.mem_append_left right member)
  intro current valid root member
  split
  · exact valid
  · intro atom included
    rcases List.mem_append.mp included with earlier | added
    · exact valid earlier
    · have equal : atom = root := by simpa using added
      subst atom
      exact List.mem_append_right left member

theorem normalize_join_known (f : Func) (left right : Roots) (leftRoots rightRoots : List RootRef)
    (leftKnown : normalize f left = some leftRoots)
    (rightKnown : normalize f right = some rightRoots) :
    ∃ actual, normalize f (left.join right) = some actual ∧
      ∀ root ∈ actual, root ∈ leftRoots ∨ root ∈ rightRoots := by
  cases left with
  | pending => simp [normalize] at leftKnown
  | unknown => simp [normalize] at leftKnown
  | known left =>
    cases right with
    | pending => simp [normalize] at rightKnown
    | unknown => simp [normalize] at rightKnown
    | known right =>
      obtain ⟨_, leftAtoms⟩ := normalize_fold_atoms f left [] leftRoots leftKnown
      obtain ⟨_, rightAtoms⟩ := normalize_fold_atoms f right [] rightRoots rightKnown
      obtain ⟨joined, equation, included⟩ := join_known_subset left right
      obtain ⟨actual, result, within⟩ := normalize_fold_within f joined (leftRoots ++ rightRoots) (by
        intro atom member
        rcases List.mem_append.mp (included member) with first | second
        · obtain ⟨roots, known, bound⟩ := leftAtoms atom first
          exact ⟨roots, known, fun root member => List.mem_append_left rightRoots (bound member)⟩
        · obtain ⟨roots, known, bound⟩ := rightAtoms atom second
          exact ⟨roots, known, fun root member => List.mem_append_right leftRoots (bound member)⟩)
        [] (by simp)
      exact ⟨actual, by rw [equation]; exact result, fun root member => List.mem_append.mp (within member)⟩

#print axioms normalizeAtom_ofRootRef
#print axioms normalize_rootMap
#print axioms unionRoots_mem_iff
#print axioms fold_expanded_roots_mem
#print axioms normalize_rootMap_known
#print axioms normalize_rootMap_dedup_known
#print axioms normalize_join_known

end Goose.GIR.ReplacementContentFlow.Model
