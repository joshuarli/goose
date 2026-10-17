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

#print axioms normalizeAtom_ofRootRef
#print axioms normalize_rootMap
#print axioms unionRoots_mem_iff
#print axioms fold_expanded_roots_mem
#print axioms normalize_rootMap_known
#print axioms normalize_rootMap_dedup_known

end Goose.GIR.ReplacementContentFlow.Model
