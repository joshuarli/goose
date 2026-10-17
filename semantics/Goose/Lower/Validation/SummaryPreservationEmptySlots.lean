import Goose.Lower.Validation.SummaryPreservationTypedSlots

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rootsRefine_empty_typed_slot_bound {module : Core.Module} {ctx : Context} {impl : Impl}
    {slot : SlotId} {localVar : LocalVar} {actual : List RootRef}
    (checked : checkAnnotationShape module impl ctx = .ok ())
    (variableRow : impl.vars[slot]? = some localVar) (ordinary : localVar.ty.isRefSlice = false)
    (refined : RootsRefine (lowerContextAt module ctx impl) actual []) :
    ∀ root ∈ actual, root ∈ rootsAt (typedContextSlotUpper module ctx impl) slot := by
  simp only [typedContextSlotUpper_at variableRow, ordinary, Bool.false_eq_true, ite_false]
  apply rootsRefine_context_upper (refined.source_mono (by simp))
  cases found : ctx.varRoots.find? (·.1 == slot) with
  | none => simp
  | some row =>
    exact annotation_parameter_bounds (slot := slot) (annotation := row.2) checked (by simp [found])

end Goose.Lower.Validation.SummaryPreservation
