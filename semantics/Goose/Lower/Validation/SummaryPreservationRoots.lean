import Goose.Lower.Validation.SummaryPreservationSource

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound

theorem mem_unionRoots_iff {left right : List RootRef} {root : RootRef} :
    root ∈ unionRoots left right ↔ root ∈ left ∨ root ∈ right :=
  ⟨unionRoots_mem left right root, fun member => member.elim
    (unionRoots_left left right root) (unionRoots_right left right root)⟩

theorem mem_fold_unionRoots {sets : List (List RootRef)} {initial : List RootRef}
    {root : RootRef} :
    root ∈ sets.foldl unionRoots initial ↔ root ∈ initial ∨ ∃ roots ∈ sets, root ∈ roots := by
  induction sets generalizing initial with
  | nil => simp
  | cons roots rest ih =>
    simp only [List.foldl_cons, ih, mem_unionRoots_iff, List.mem_cons]
    constructor
    · rintro ((member | member) | ⟨set, member, rootMember⟩)
      · exact Or.inl member
      · exact Or.inr ⟨roots, Or.inl rfl, member⟩
      · exact Or.inr ⟨set, Or.inr member, rootMember⟩
    · rintro (member | ⟨set, rfl | member, rootMember⟩)
      · exact Or.inl (Or.inl member)
      · exact Or.inl (Or.inr rootMember)
      · exact Or.inr ⟨set, member, rootMember⟩

theorem mem_fold_unionRoots_empty {sets : List (List RootRef)} {root : RootRef} :
    root ∈ sets.foldl unionRoots [] ↔ ∃ roots ∈ sets, root ∈ roots := by
  simp [mem_fold_unionRoots]

theorem lowerContextRootInfo_result_eq {ctx : Context} {impl : Impl}
    {result : Nat} (bound : result < impl.results.size) :
    (lowerContextRootInfo ctx impl).results[result]? = some
      (unionRoots (ctx.resultRoots[result]?.getD [])
        (impl.params.toList.zipIdx.filterMap fun (param, position) =>
          match ctx.varRoots.find? (·.1 == param.var) with
          | some (_, paramRoots) =>
            if paramRoots.all (ctx.resultRoots[result]?.getD []).contains then
              some (.param position) else none
          | none => none)) := by
  simp [lowerContextRootInfo, lowerContextRootCeiling, bound]
  rfl

theorem lowerContextRootInfo_result_contains {ctx : Context} {impl : Impl}
    {result : Nat} {roots : List RootRef}
    (bound : result < impl.results.size) (lookup : ctx.resultRoots[result]? = some roots) :
    ∀ root ∈ roots,
      root ∈ ((lowerContextRootInfo ctx impl).results[result]?).getD [] := by
  intro root member
  rw [lowerContextRootInfo_result_eq bound]
  simp only [Option.getD_some, lookup]
  exact unionRoots_left _ _ root member

theorem accepted_context_result_roots_preserved {module : Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {result : Nat} {roots : List RootRef}
    (accepted : validate module = .ok ()) (contextLookup : module.contexts[context]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl)
    (rootsLookup : ctx.resultRoots[result]? = some roots) :
    ∀ root ∈ roots,
      root ∈ ((lowerContextAt module ctx impl).roots.results[result]?).getD [] := by
  obtain ⟨checkedImpl, lookup, checked⟩ := (validate_modOk module accepted).ctx context ctx contextLookup
  rw [implLookup] at lookup
  cases lookup
  have bound : result < impl.results.size := by
    rw [← checked.resultLen]
    exact (List.getElem?_eq_some_iff.mp rootsLookup).1
  exact lowerContextRootInfo_result_contains bound rootsLookup

end Goose.Lower.Validation.SummaryPreservation
