import Goose.GIR.RootSeeds
import Goose.Lower.Validation.SummaryPreservationTypedSlots
import Goose.Lower.Validation.SummaryPreservationTypedResultBounds

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerContextRootCeiling_below_refined (module : Core.Module) (ctx : Context) (impl : Impl)
    (declared : List RootRef) :
    ∀ root ∈ lowerContextRootCeiling ctx impl declared,
      root ∈ refinedResultUpper (lowerContextAt module ctx impl) declared := by
  intro root member
  rcases mem_unionRoots_iff.mp member with literal | alias
  · exact unionRoots_left _ _ _ literal
  · obtain ⟨⟨param, index⟩, parameterMember, selected⟩ := List.mem_filterMap.mp alias
    have parameterRow : impl.params[index]? = some param := by
      simpa only [Array.getElem?_toList] using List.mk_mem_zipIdx_iff_getElem?.mp parameterMember
    cases annotation : ctx.varRoots.find? (·.1 == param.var) with
    | none => simp [annotation] at selected
    | some entry =>
      simp only [annotation] at selected
      split at selected
      · rename_i subset
        cases Option.some.inj selected
        apply unionRoots_right
        apply allowedRoots_complete (actual := [.param index])
        · intro candidate candidateMember concrete concreteMember
          have same : candidate = .param index := List.mem_singleton.mp candidateMember
          subst candidate
          have parameterRoots := lowerContextAt_parameterRoots_eq (module := module) (ctx := ctx)
            parameterRow (roots := entry.2) (by simp [annotation])
          exact subsetRoots_mem subset concrete (by simpa only [Func.expandParameterRoot, parameterRoots] using concreteMember)
        · intro candidate candidateMember
          have same : candidate = index := RootRef.param.inj (List.mem_singleton.mp candidateMember)
          subst candidate
          simpa only [lowerContextAt, lowerImpl, List.length_map, Array.length_toList] using
            (Array.getElem?_eq_some_iff.mp parameterRow).1
        · simp
      · simp at selected

theorem annotation_find_of_row {module : Core.Module} {ctx : Context} {impl : Impl}
    {slot : VarId} {declared : List RootRef} {localVar : LocalVar}
    (checked : checkAnnotationShape module impl ctx = .ok ())
    (variableRow : impl.vars[slot]? = some localVar) (reference : localVar.ty.isRefLike = true)
    (row : (slot, declared) ∈ ctx.varRoots) :
    ctx.varRoots.find? (·.1 == slot) = some (slot, declared) := by
  have count := (Core.Declarative.annotations_sound module impl ctx checked).2.1 slot localVar variableRow reference
  obtain ⟨entry, filtered⟩ := List.length_eq_one_iff.mp count
  have member : (slot, declared) ∈ ctx.varRoots.filter (·.1 == slot) := List.mem_filter.mpr ⟨row, by simp⟩
  rw [filtered] at member
  have same : (slot, declared) = entry := List.mem_singleton.mp member
  rw [← List.head?_filter, filtered, ← same]
  rfl

theorem lowerContext_slotRootSeeds_below {module : Core.Module} {ctx : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (checked : checkAnnotationShape module impl ctx = .ok ()) :
    RootsBelow (lowerContextAt module ctx impl).slotRootSeeds (typedContextSlotUpper module ctx impl) := by
  intro slot root member
  simp only [rootsAt, Func.slotRootSeeds, Array.getElem?_mapIdx] at member
  cases slotRow : (lowerContextAt module ctx impl).slots[slot]? with
  | none => simp [slotRow] at member
  | some descriptor =>
    simp only [slotRow, Option.map_some, Option.getD_some] at member
    have rows : ∀ row ∈ (lowerContextAt module ctx impl).roots.slots.getD #[],
        row.1 = slot → ∀ item ∈ row.2, item ∈ rootsAt (typedContextSlotUpper module ctx impl) slot := by
      intro row member same item itemMember
      change row ∈ (ctx.varRoots.filterMap fun (slot, roots) =>
        match impl.vars[slot]? with
        | some localVar => if !localVar.ty.isRefLike then none
          else some (slot, if localVar.ty.isRefSlice && (impl.params[slot]?).any (·.var == slot) then [.param slot]
            else lowerContextRootCeiling ctx impl roots)
        | none => none).toArray at member
      obtain ⟨⟨index, declared⟩, annotationMember, selected⟩ := List.mem_filterMap.mp (Array.mem_toList_iff.mpr member)
      cases variableRow : impl.vars[index]? with
      | none => simp [variableRow] at selected
      | some localVar =>
        by_cases reference : localVar.ty.isRefLike = true
        · simp only [variableRow, reference, Bool.not_true, Bool.false_eq_true, ite_false, Option.some.injEq] at selected
          subst row
          dsimp only at same itemMember
          subst index
          rw [typedContextSlotUpper_at variableRow]
          by_cases refSlice : localVar.ty.isRefSlice = true
          · obtain ⟨param, parameterRow, identity, _⟩ :=
              accepted_refSlice_parameter accepted implementationRow variableRow refSlice
            simpa [refSlice, parameterRow, identity] using itemMember
          · simp only [refSlice, Bool.false_eq_true, ite_false] at itemMember ⊢
            have annotation := annotation_find_of_row checked variableRow reference annotationMember
            simpa only [annotation, Option.map_some, Option.getD_some] using
              lowerContextRootCeiling_below_refined module ctx impl declared item itemMember
        · simp [variableRow, reference] at selected
    have foldBound : ∀ initial, (∀ item ∈ initial, item ∈ rootsAt (typedContextSlotUpper module ctx impl) slot) →
        ∀ item ∈ ((lowerContextAt module ctx impl).roots.slots.getD #[]).toList.foldl
          (fun roots row => if row.1 == slot then unionRoots roots row.2 else roots) initial,
          item ∈ rootsAt (typedContextSlotUpper module ctx impl) slot := by
      intro initial initialBound
      apply List.foldlRecOn (motive := fun roots => ∀ item ∈ roots, item ∈ rootsAt (typedContextSlotUpper module ctx impl) slot)
        _ _ initialBound
      intro accumulated prior row member
      by_cases same : row.1 == slot
      · rw [if_pos same]
        intro item itemMember
        exact (mem_unionRoots_iff.mp itemMember).elim (prior item)
          (rows row (Array.mem_toList_iff.mp member) (eq_of_beq same) item)
      · simpa only [same, Bool.false_eq_true, ite_false] using prior
    exact foldBound [] (by simp) root (by simpa only [Array.foldl_toList] using member)

theorem lower_declaredResultRoots_below (module : Core.Module) :
    RootsBelow (lower module).declaredResultRoots (moduleTypedResultUpper module) := by
  intro index root member
  cases contextRow : module.contexts[index]? with
  | none => simp [rootsAt, Module.declaredResultRoots, lower, Array.getElem?_map, contextRow] at member
  | some ctx =>
    cases implementationRow : module.impls[ctx.impl]? with
    | none => simp [rootsAt, Module.declaredResultRoots, lower, Array.getElem?_map, contextRow, implementationRow,
        invalidContextFunction] at member
    | some impl =>
      have functionRow := lower_func_at contextRow implementationRow
      simp only [rootsAt, Module.declaredResultRoots, Array.getElem?_map, functionRow,
        Option.map_some, Option.getD_some] at member
      have results : (lowerContextAt module ctx impl).results = impl.results.toList := rfl
      rw [results] at member
      cases resultTypes : impl.results.toList with
      | nil => simp [resultTypes] at member
      | cons type rest =>
        cases rest with
        | cons second rest => simp [resultTypes] at member
        | nil =>
          have resultAt : impl.results[0]? = some type := by
            rw [← Array.getElem?_toList, resultTypes]
            rfl
          have sourcePresent : (lowerContextAt module ctx impl).roots.slots.isSome = true := rfl
          by_cases reference : type.isRefLike = true
          · simp only [resultTypes, sourcePresent, Bool.true_and, reference, ite_true] at member
            have bound : 0 < impl.results.size := (Array.getElem?_eq_some_iff.mp resultAt).1
            have projected : ((lowerContextAt module ctx impl).roots.results[0]?).getD [] =
                lowerContextRootCeiling ctx impl (ctx.resultRoots[0]?.getD []) := by
              change ((lowerContextRootInfo ctx impl).results[0]?).getD [] = _
              rw [lowerContextRootInfo_result_eq bound]
              rfl
            rw [projected] at member
            have upper := lowerContextRootCeiling_below_refined module ctx impl _ root member
            simpa only [rootsAt, moduleTypedResultUpper, Array.getElem?_map, contextRow,
              Option.map_some, Option.getD_some, contextTypedResultUpper, implementationRow,
              resultAt, Option.any_some, reference, ite_true, contextRefinedResultUpper] using upper
          · simp [resultTypes, reference] at member

#print axioms lowerContextRootCeiling_below_refined
#print axioms annotation_find_of_row
#print axioms lowerContext_slotRootSeeds_below
#print axioms lower_declaredResultRoots_below

end Goose.Lower.Validation.SummaryPreservation
