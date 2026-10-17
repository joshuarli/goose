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

theorem lowerRootInfo_result_eq {module : Module} {index : ImplId} {impl : Impl}
    {result : Nat} (bound : result < impl.results.size) :
    (lowerRootInfo module index impl).results[result]? = some
      (((module.contexts.filter (·.impl == index)).filterMap fun ctx => do
        let roots ← ctx.resultRoots[result]?
        let parameterRoots := impl.params.toList.zipIdx.filterMap fun (param, position) =>
          match ctx.varRoots.find? (·.1 == param.var) with
          | some (_, paramRoots) =>
            if roots.any paramRoots.contains then some (.param position) else none
          | none => none
        some (unionRoots roots parameterRoots)).foldl unionRoots []) := by
  simp [lowerRootInfo, bound]
  rfl

theorem lowerRootInfo_result_contains_context {module : Module} {index : ImplId} {impl : Impl}
    {ctx : Context} {result : Nat} {roots : List RootRef}
    (member : ctx ∈ module.contexts.toList) (identity : ctx.impl = index)
    (bound : result < impl.results.size) (lookup : ctx.resultRoots[result]? = some roots) :
    ∀ root ∈ roots,
      root ∈ ((lowerRootInfo module index impl).results[result]?).getD [] := by
  intro root rootMember
  rw [lowerRootInfo_result_eq bound]
  simp only [Option.getD_some]
  rw [← Array.foldl_toList, mem_fold_unionRoots_empty]
  let parameters := impl.params.toList.zipIdx.filterMap fun (param, position) =>
    match ctx.varRoots.find? (·.1 == param.var) with
    | some (_, paramRoots) =>
      if roots.any paramRoots.contains then some (RootRef.param position) else none
    | none => none
  refine ⟨unionRoots roots parameters, ?_, unionRoots_left _ _ _ rootMember⟩
  simp only [Array.toList_filterMap, Array.toList_filter, List.mem_filterMap]
  refine ⟨ctx, List.mem_filter.mpr ⟨member, by simp [identity]⟩, ?_⟩
  simp [lookup, parameters]

theorem accepted_context_result_roots_preserved {module : Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {result : Nat} {roots : List RootRef}
    (accepted : validate module = .ok ()) (contextLookup : module.contexts[context]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl)
    (rootsLookup : ctx.resultRoots[result]? = some roots) :
    ∀ root ∈ roots,
      root ∈ ((lowerImplAt module ctx.impl impl).roots.results[result]?).getD [] := by
  obtain ⟨checkedImpl, lookup, checked⟩ := (validate_modOk module accepted).ctx context ctx contextLookup
  rw [implLookup] at lookup
  cases lookup
  have bound : result < impl.results.size := by
    rw [← checked.resultLen]
    exact (List.getElem?_eq_some_iff.mp rootsLookup).1
  exact lowerRootInfo_result_contains_context
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? contextLookup)) rfl bound rootsLookup

end Goose.Lower.Validation.SummaryPreservation
