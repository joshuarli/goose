import Goose.Lower.Validation.SummaryPreservationDeclaredSeeds

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR


theorem refinedResultUpper_below_ceiling (module : Core.Module) (ctx : Context) (impl : Impl)
    (declared : List RootRef) :
    ∀ root ∈ refinedResultUpper (lowerContextAt module ctx impl) declared,
      root ∈ lowerContextRootCeiling ctx impl declared := by
  intro root member
  rcases mem_unionRoots_iff.mp member with literal | allowed
  · exact unionRoots_left _ _ root literal
  · rcases List.mem_append.mp allowed with direct | alias
    · obtain ⟨source, sourceMember, mapped⟩ := List.mem_filterMap.mp direct
      have included : source ∈ lowerContextRootCeiling ctx impl declared := unionRoots_left _ _ _ sourceMember
      cases source <;> simp_all
    · obtain ⟨index, indexMember, selected⟩ := List.mem_filterMap.mp alias
      split at selected
      · rename_i subset
        cases Option.some.inj selected
        apply lowerContextRootCeiling_parameter _ subset
        have bound := List.mem_range.mp indexMember
        simpa [lowerContextAt, lowerImpl, lowerImplFromState] using bound
      · simp at selected

theorem typedContextSlotUpper_below_declared_row {module : Core.Module} {ctx : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (checked : checkAnnotationShape module impl ctx = .ok ())
    {row : SlotId × List RootRef}
    (member : row ∈ (lowerContextAt module ctx impl).roots.slots.getD #[]) :
    ∀ root ∈ rootsAt (typedContextSlotUpper module ctx impl) row.1, root ∈ row.2 := by
  change row ∈ (ctx.varRoots.filterMap fun (slot, roots) =>
    match impl.vars[slot]? with
    | some localVar => if !localVar.ty.isRefLike then none
      else some (slot, if localVar.ty.isRefSlice && (impl.params[slot]?).any (·.var == slot) then [.param slot]
        else lowerContextRootCeiling ctx impl roots)
    | none => none).toArray at member
  obtain ⟨⟨slot, declared⟩, annotationMember, selected⟩ := List.mem_filterMap.mp (Array.mem_toList_iff.mpr member)
  cases variableRow : impl.vars[slot]? with
  | none => simp [variableRow] at selected
  | some localVar =>
    by_cases reference : localVar.ty.isRefLike = true
    · simp only [variableRow, reference, Bool.not_true, Bool.false_eq_true, ite_false, Option.some.injEq] at selected
      subst row
      rw [typedContextSlotUpper_at variableRow]
      by_cases refSlice : localVar.ty.isRefSlice = true
      · obtain ⟨param, parameterRow, identity, _⟩ :=
          accepted_refSlice_parameter accepted implementationRow variableRow refSlice
        simp only [refSlice, parameterRow, Option.any_some, identity, beq_self_eq_true, Bool.and_self, ite_true]
        exact fun _ member => member
      · simp only [refSlice, Bool.false_eq_true, ite_false, Bool.false_and]
        have annotation := annotation_find_of_row checked variableRow reference annotationMember
        simpa only [annotation, Option.map_some, Option.getD_some] using
          refinedResultUpper_below_ceiling module ctx impl declared
    · simp [variableRow, reference] at selected

theorem lowerContext_declared_slot_reference {module : Core.Module} {ctx : Context} {impl : Impl}
    {row : SlotId × List RootRef}
    (member : row ∈ (lowerContextAt module ctx impl).roots.slots.getD #[]) :
    ∃ storage, (lowerContextAt module ctx impl).slots[row.1]? = some storage ∧
      storage.ty.isRefLike = true := by
  change row ∈ (ctx.varRoots.filterMap fun (slot, roots) =>
    match impl.vars[slot]? with
    | some localVar => if !localVar.ty.isRefLike then none
      else some (slot, if localVar.ty.isRefSlice && (impl.params[slot]?).any (·.var == slot) then [.param slot]
        else lowerContextRootCeiling ctx impl roots)
    | none => none).toArray at member
  obtain ⟨⟨slot, declared⟩, annotation, selected⟩ := List.mem_filterMap.mp (Array.mem_toList_iff.mpr member)
  cases variableRow : impl.vars[slot]? with
  | none => simp [variableRow] at selected
  | some localVar =>
    by_cases reference : localVar.ty.isRefLike = true
    · simp only [variableRow, reference, Bool.not_true, Bool.false_eq_true, ite_false, Option.some.injEq] at selected
      subst row
      refine ⟨⟨localVar.ty, localVar.kind, localVar.scope, slot⟩, ?_, reference⟩
      change (impl.vars.mapIdx fun index localVar => (⟨localVar.ty, localVar.kind, localVar.scope, index⟩ : Slot))[slot]? = _
      simp only [Array.getElem?_mapIdx, variableRow, Option.map_some]
    · simp [variableRow, reference] at selected

#print axioms refinedResultUpper_below_ceiling
#print axioms typedContextSlotUpper_below_declared_row
#print axioms lowerContext_declared_slot_reference

end Goose.Lower.Validation.SummaryPreservation
