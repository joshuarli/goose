import Goose.Lower.Validation.SummaryPreservationVariableShape
import Goose.Lower.Validation.SummaryPreservationRefinedResults

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def typedContextSlotUpper (module : Core.Module) (ctx : Context) (impl : Impl) : Array (List RootRef) :=
  impl.vars.mapIdx fun slot localVar =>
    if localVar.ty.isRefSlice then [.param slot]
    else refinedResultUpper (lowerContextAt module ctx impl)
      ((ctx.varRoots.find? (·.1 == slot)).map (·.2) |>.getD [])


theorem typedContextSlotUpper_at {module : Core.Module} {ctx : Context} {impl : Impl}
    {slot : SlotId} {localVar : LocalVar} (lookup : impl.vars[slot]? = some localVar) :
    rootsAt (typedContextSlotUpper module ctx impl) slot =
      if localVar.ty.isRefSlice then [.param slot]
      else refinedResultUpper (lowerContextAt module ctx impl)
        ((ctx.varRoots.find? (·.1 == slot)).map (·.2) |>.getD []) := by
  simp [rootsAt, typedContextSlotUpper, Array.getElem?_mapIdx, lookup]


theorem typedContextSlotUpper_refines {module : Core.Module} {ctx : Context} {impl : Impl}
    {implementation : ImplId} {slot : SlotId} {localVar : LocalVar} {annotation : List RootRef}
    (accepted : Core.validate module = .ok ()) (implementationRow : module.impls[implementation]? = some impl)
    (variableRow : impl.vars[slot]? = some localVar)
    (annotationRow : (ctx.varRoots.find? (·.1 == slot)).map (·.2) = some annotation) :
    RootsRefine (lowerContextAt module ctx impl) (rootsAt (typedContextSlotUpper module ctx impl) slot)
      annotation := by
  rw [typedContextSlotUpper_at variableRow]
  split
  · rename_i reference
    obtain ⟨param, parameterRow, identity, _⟩ := accepted_refSlice_parameter
      accepted implementationRow variableRow reference
    have parameterRoots := lowerContextAt_parameterRoots_eq (module := module) parameterRow
      (by simpa [identity] using annotationRow)
    intro root member
    have same : root = .param slot := List.mem_singleton.mp member
    subst root
    exact Or.inr (by simpa only [Func.expandParameterRoot, parameterRoots] using
      (fun concrete (h : concrete ∈ annotation) => h))
  · rw [annotationRow]
    exact refinedResultUpper_refines _ _


theorem typedContextSlotUpper_parameter {module : Core.Module} {ctx : Context} {impl : Impl}
    {slot : SlotId} {param : Param} {localVar : LocalVar} {annotation : List RootRef}
    (parameterRow : impl.params[slot]? = some param) (identity : param.var = slot)
    (variableRow : impl.vars[slot]? = some localVar)
    (annotationRow : (ctx.varRoots.find? (·.1 == slot)).map (·.2) = some annotation) :
    RootRef.param slot ∈ rootsAt (typedContextSlotUpper module ctx impl) slot := by
  rw [typedContextSlotUpper_at variableRow]
  split
  · simp
  · rw [annotationRow]
    apply unionRoots_right
    have represented : RootsRepresent (lowerContextAt module ctx impl) [.param slot] annotation := by
      have parameters := lowerContextAt_parameterRoots_eq (module := module) parameterRow
        (by simpa [identity] using annotationRow)
      intro root member concrete concreteMember
      have same : root = .param slot := List.mem_singleton.mp member
      subst root
      simpa only [Func.expandParameterRoot, parameters] using concreteMember
    apply allowedRoots_complete represented _ (.param slot) (by simp)
    intro index member
    have same : index = slot := RootRef.param.inj (List.mem_singleton.mp member)
    subst index
    simpa [lowerContextAt, lowerImpl, lowerImplFromState] using (Array.getElem?_eq_some_iff.mp parameterRow).1


theorem annotation_parameter_bounds {module : Core.Module} {ctx : Context} {impl : Impl}
    {slot : SlotId} {annotation : List RootRef}
    (checked : checkAnnotationShape module impl ctx = .ok ())
    (annotationRow : (ctx.varRoots.find? (·.1 == slot)).map (·.2) = some annotation) :
    ∀ index, RootRef.param index ∈ annotation → index < impl.params.size := by
  cases found : ctx.varRoots.find? (·.1 == slot) with
  | none => simp [found] at annotationRow
  | some row =>
    simp only [found, Option.map_some, Option.some.injEq] at annotationRow
    obtain ⟨_, _, _, bounds⟩ := Core.Declarative.annotationRows_sound module impl ctx checked
      row.1 row.2 (List.mem_of_find?_eq_some found)
    intro index member
    rw [← annotationRow] at member
    exact bounds (.param index) member


theorem bindRootsV_typed_slot_bound {module : Core.Module} {ctx : Context} {impl : Impl}
    {scopes chain : List Nat} {slot : SlotId} {localVar : LocalVar} {actual source : List RootRef}
    (checkedAnnotations : checkAnnotationShape module impl ctx = .ok ())
    (variableRow : impl.vars[slot]? = some localVar) (ordinary : localVar.ty.isRefSlice = false)
    (checked : bindRootsV ⟨module, impl, ctx, scopes⟩ chain slot source = .ok ())
    (refined : RootsRefine (lowerContextAt module ctx impl) actual source) :
    ∀ root ∈ actual, root ∈ rootsAt (typedContextSlotUpper module ctx impl) slot := by
  obtain ⟨boundVar, annotation, boundRow, annotationRow, subset, _⟩ := bindRootsV_ok _ _ _ _ checked
  rw [variableRow] at boundRow
  cases boundRow
  change (ctx.varRoots.find? (·.1 == slot)).map (·.2) = some annotation at annotationRow
  simp only [typedContextSlotUpper_at variableRow, ordinary, Bool.false_eq_true, ite_false,
    annotationRow, Option.getD_some]
  exact rootsRefine_context_upper (refined.source_mono subset)
    (annotation_parameter_bounds checkedAnnotations annotationRow)

end Goose.Lower.Validation.SummaryPreservation
