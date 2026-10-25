import Goose.Lower.Validation.SourceRootAnnotationsAccepted
import Goose.Lower.Validation.SummaryPreservationModuleEffects

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource

theorem accepted_function_checkSummaryOf {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (index : Nat) :
    checkSummaryOf (lower module) (lower module).implTypes
      (resultRoots (lower module) (lower module).implTypes) (lower module).rootCount index = .ok () := by
  cases functionAt : (lower module).funcs[index]? with
  | none => simp [checkSummaryOf, functionAt, pure, Except.pure]
  | some func =>
    obtain ⟨context, impl, contextAt, implAt, same⟩ := accepted_function_context accepted functionAt
    have roots := accepted_context_checkRootAnnotationsOf accepted contextAt implAt
    have effects := accepted_module_function_summaryClosed accepted functionAt
    simp only [checkSummaryOf, functionAt, roots, bind, Except.bind]
    simp only [effects, asCheck, pure, Except.pure]

private theorem checkAll_of_all {items : List α} {action : α → Check Unit}
    (checked : ∀ item ∈ items, action item = .ok ()) : checkAll items action = .ok () := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    rw [checkAll, checked first (by simp)]
    exact ih (fun item member => checked item (by simp [member]))

theorem accepted_module_checkSummaries {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    checkAll (List.range (lower module).funcs.size)
      (checkSummaryOf (lower module) (lower module).implTypes
        (resultRoots (lower module) (lower module).implTypes) (lower module).rootCount) = .ok () :=
  checkAll_of_all (fun index _ => accepted_function_checkSummaryOf accepted index)

#print axioms accepted_function_checkSummaryOf
#print axioms accepted_module_checkSummaries

end Goose.Lower.Validation
