import Goose.GIR.Effects
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

private theorem find_filterMap_zipIdx_eq {α β : Type} {items : List α} {index : Nat}
    {item : α} (select : α → Nat → Option β) (lookup : items[index]? = some item) :
    ((items.zipIdx.filterMap fun (item, index) =>
      (select item index).map (index, ·)).find? (·.1 == index)) =
        (select item index).map (index, ·) := by
  cases selected : select item index with
  | some value =>
    exact find_filterMap_zipIdx select lookup selected
  | none =>
    simp only [Option.map_none]
    apply List.find?_eq_none.mpr
    intro row member key
    have indexEq : row.1 = index := eq_of_beq key
    obtain ⟨⟨source, position⟩, sourceMember, mapped⟩ := List.mem_filterMap.mp member
    have sourceLookup := List.mk_mem_zipIdx_iff_getElem?.mp sourceMember
    cases choice : select source position with
    | none => simp [choice] at mapped
    | some value =>
      simp only [choice, Option.map_some, Option.some.injEq] at mapped
      cases mapped
      simp only at indexEq
      subst position
      rw [lookup] at sourceLookup
      cases sourceLookup
      rw [selected] at choice
      cases choice

theorem lowerContextRootInfo_parameter_lookup {impl : Impl} {ctx : Context}
    {index : Nat} {param : Param} (parameter : impl.params[index]? = some param) :
    ((lowerContextRootInfo ctx impl).params.find? (·.1 == index)) =
      (ctx.varRoots.find? (·.1 == param.var)).map (fun row => (index, row.2)) := by
  have row := find_filterMap_zipIdx_eq
    (items := impl.params.toList) (index := index) (item := param)
    (fun (param : Param) _ => (ctx.varRoots.find? (·.1 == param.var)).map (·.2))
    (by simpa using parameter)
  simpa only [lowerContextRootInfo, ← Array.find?_toList, List.toList_toArray,
    Option.map_map, Function.comp_def] using row

theorem lowerContextRootInfo_contents_lookup {impl : Impl} {ctx : Context}
    {index : Nat} {param : Param} (parameter : impl.params[index]? = some param) :
    ((lowerContextRootInfo ctx impl).contents.find? (·.1 == index)) =
      (ctx.contentRoots.find? (·.1 == param.var)).map (fun row => (index, row.2)) := by
  have row := find_filterMap_zipIdx_eq
    (items := impl.params.toList) (index := index) (item := param)
    (fun (param : Param) _ => (ctx.contentRoots.find? (·.1 == param.var)).map (·.2))
    (by simpa using parameter)
  simpa only [lowerContextRootInfo, ← Array.find?_toList, List.toList_toArray,
    Option.map_map, Function.comp_def] using row

theorem lowerContextRootInfo_parameter_eq {impl : Impl} {ctx : Context}
    {index : Nat} {param : Param} {roots : List RootRef}
    (parameter : impl.params[index]? = some param)
    (annotation : (ctx.varRoots.find? (·.1 == param.var)).map (·.2) = some roots) :
    ((lowerContextRootInfo ctx impl).params.find? (·.1 == index)) = some (index, roots) := by
  have row := find_filterMap_zipIdx
    (items := impl.params.toList) (index := index) (item := param) (value := roots)
    (fun (param : Param) _ => (ctx.varRoots.find? (·.1 == param.var)).map (·.2))
    (by simpa using parameter) annotation
  simpa only [lowerContextRootInfo, ← Array.find?_toList, List.toList_toArray,
    Option.map_map, Function.comp_def] using row

theorem lowerContextRootInfo_contents_eq {impl : Impl} {ctx : Context}
    {index : Nat} {param : Param} {roots : List RootRef}
    (parameter : impl.params[index]? = some param)
    (annotation : (ctx.contentRoots.find? (·.1 == param.var)).map (·.2) = some roots) :
    ((lowerContextRootInfo ctx impl).contents.find? (·.1 == index)) = some (index, roots) := by
  have row := find_filterMap_zipIdx
    (items := impl.params.toList) (index := index) (item := param) (value := roots)
    (fun (param : Param) _ => (ctx.contentRoots.find? (·.1 == param.var)).map (·.2))
    (by simpa using parameter) annotation
  simpa only [lowerContextRootInfo, ← Array.find?_toList, List.toList_toArray,
    Option.map_map, Function.comp_def] using row

theorem lowerContextAt_parameterRoots_eq {module : Module} {impl : Impl} {ctx : Context}
    {index : Nat} {param : Param} {roots : List RootRef}
    (parameter : impl.params[index]? = some param)
    (annotation : (ctx.varRoots.find? (·.1 == param.var)).map (·.2) = some roots) :
    (lowerContextAt module ctx impl).parameterRoots index = roots := by
  change (match (lowerContextRootInfo ctx impl).params.find? (·.1 == index) with
    | some (_, roots) => roots
    | none => [.param index]) = roots
  rw [lowerContextRootInfo_parameter_eq parameter annotation]

end Goose.Lower.Validation.SummaryPreservation
