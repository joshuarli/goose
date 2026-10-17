import Goose.Lower.Validation.SummaryPreservationRoots

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound

private theorem find_filterMap_zipIdx {α β : Type} {items : List α} {index : Nat}
    {item : α} {value : β} (select : α → Nat → Option β)
    (lookup : items[index]? = some item) (selected : select item index = some value) :
    ((items.zipIdx.filterMap fun (item, index) =>
      (select item index).map (index, ·)).find? (·.1 == index)) = some (index, value) := by
  let rows := items.zipIdx.filterMap fun (item, index) =>
    (select item index).map (index, ·)
  have member : (index, value) ∈ rows := by
    apply List.mem_filterMap.mpr
    exact ⟨(item, index), List.mk_mem_zipIdx_iff_getElem?.mpr lookup, by simp [selected]⟩
  change rows.find? (·.1 == index) = some (index, value)
  cases found : rows.find? (·.1 == index) with
  | none =>
    have absent := List.find?_eq_none.mp found (index, value) member
    simp at absent
  | some row =>
    have key : row.1 = index := eq_of_beq (List.find?_some (p := fun candidate : Nat × β => candidate.1 == index) (a := row) found)
    obtain ⟨⟨source, position⟩, sourceMember, mapped⟩ :=
      List.mem_filterMap.mp (List.mem_of_find?_eq_some found)
    have sourceLookup := List.mk_mem_zipIdx_iff_getElem?.mp sourceMember
    cases choice : select source position with
    | none => simp [choice] at mapped
    | some selectedValue =>
      simp only [choice, Option.map_some, Option.some.injEq] at mapped
      cases mapped
      simp only at key
      subst position
      rw [lookup] at sourceLookup
      cases sourceLookup
      rw [selected] at choice
      cases choice
      rfl

private theorem merged_annotation_contains {module : Module} {implId : ImplId} {impl : Impl}
    {ctx : Context} {index : Nat} {param : Param} {roots : List RootRef}
    (annotations : Context → List (VarId × List RootRef))
    (member : ctx ∈ module.contexts.toList) (identity : ctx.impl = implId)
    (parameter : impl.params[index]? = some param)
    (annotation : ((annotations ctx).find? (·.1 == param.var)).map (·.2) = some roots) :
    ∃ merged,
      ((impl.params.toList.zipIdx.filterMap fun (param, index) =>
        let sets := (module.contexts.filter (·.impl == implId)).filterMap fun ctx =>
          ((annotations ctx).find? (·.1 == param.var)).map (·.2)
        if sets.isEmpty then none else some (index, sets.foldl unionRoots [])).find?
          (·.1 == index)) = some (index, merged) ∧
      ∀ root ∈ roots, root ∈ merged := by
  let sets := (module.contexts.filter (·.impl == implId)).filterMap fun ctx =>
    ((annotations ctx).find? (·.1 == param.var)).map (·.2)
  have setMember : roots ∈ sets.toList := by
    simp only [sets, Array.toList_filterMap, Array.toList_filter, List.mem_filterMap]
    exact ⟨ctx, List.mem_filter.mpr ⟨member, by simp [identity]⟩, annotation⟩
  have nonempty : sets.isEmpty = false := by
    cases empty : sets.isEmpty with
    | false => rfl
    | true =>
      have sizeZero := Array.isEmpty_iff_size_eq_zero.mp empty
      have listEmpty : sets.toList = [] := by simp [List.eq_nil_iff_length_eq_zero, sizeZero]
      simp [listEmpty] at setMember
  refine ⟨sets.foldl unionRoots [], ?_, ?_⟩
  · have row := find_filterMap_zipIdx
      (items := impl.params.toList) (index := index) (item := param)
      (value := sets.foldl unionRoots [])
      (fun (param : Param) _ =>
        let sets := (module.contexts.filter (·.impl == implId)).filterMap fun ctx =>
          ((annotations ctx).find? (·.1 == param.var)).map (·.2)
        if sets.isEmpty then none else some (sets.foldl unionRoots []))
      (by simpa using parameter)
      (by change (if sets.isEmpty then none else some _) = _; simp [nonempty]; rfl)
    simpa only [apply_ite, Option.map_none, Option.map_some] using row
  · intro root rootMember
    rw [← Array.foldl_toList, mem_fold_unionRoots_empty]
    exact ⟨roots, setMember, rootMember⟩

theorem lowerRootInfo_parameter_contains_context {module : Module} {implId : ImplId}
    {impl : Impl} {ctx : Context} {index : Nat} {param : Param} {roots : List RootRef}
    (member : ctx ∈ module.contexts.toList) (identity : ctx.impl = implId)
    (parameter : impl.params[index]? = some param)
    (annotation : (ctx.varRoots.find? (·.1 == param.var)).map (·.2) = some roots) :
    ∃ merged, ((lowerRootInfo module implId impl).params.find? (·.1 == index)) =
      some (index, merged) ∧ ∀ root ∈ roots, root ∈ merged := by
  obtain ⟨merged, lookup, contains⟩ :=
    merged_annotation_contains Context.varRoots member identity parameter annotation
  refine ⟨merged, ?_, contains⟩
  simpa only [lowerRootInfo, ← Array.find?_toList, List.toList_toArray] using lookup

theorem lowerRootInfo_contents_contains_context {module : Module} {implId : ImplId}
    {impl : Impl} {ctx : Context} {index : Nat} {param : Param} {roots : List RootRef}
    (member : ctx ∈ module.contexts.toList) (identity : ctx.impl = implId)
    (parameter : impl.params[index]? = some param)
    (annotation : (ctx.contentRoots.find? (·.1 == param.var)).map (·.2) = some roots) :
    ∃ merged, ((lowerRootInfo module implId impl).contents.find? (·.1 == index)) =
      some (index, merged) ∧ ∀ root ∈ roots, root ∈ merged := by
  obtain ⟨merged, lookup, contains⟩ :=
    merged_annotation_contains Context.contentRoots member identity parameter annotation
  refine ⟨merged, ?_, contains⟩
  simpa only [lowerRootInfo, ← Array.find?_toList, List.toList_toArray] using lookup

end Goose.Lower.Validation.SummaryPreservation
