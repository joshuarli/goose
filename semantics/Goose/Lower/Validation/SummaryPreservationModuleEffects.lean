import Goose.Lower.Validation.SummaryPreservationAcceptedSummaries

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem accepted_module_function_summaryClosed {module : Core.Module} {index : Nat} {func : Func}
    (accepted : Core.validate module = .ok ())
    (functionRow : (lower module).funcs[index]? = some func) :
    func.summaryClosed (func.effects (lower module)
      (func.provenance (resultRoots (lower module) (lower module).implTypes)
        ((lower module).implTypes[index]?.getD #[]) (lower module).rootCount)) = .ok () := by
  have bound : index < module.contexts.size := by
    simpa only [lower, Array.size_map] using (Array.getElem?_eq_some_iff.mp functionRow).1
  have contextRow := Array.getElem?_eq_getElem bound
  obtain ⟨impl, implementationRow, _⟩ := (validate_modOk module accepted).ctx index _ contextRow
  have same : func = lowerContextAt module module.contexts[index] impl :=
    Option.some.inj (functionRow.symm.trans (lower_func_at contextRow implementationRow))
  subst func
  have typeRow : (lower module).implTypes[index]?.getD #[] =
      (lowerContextAt module module.contexts[index] impl).valueTypes (lower module) := by
    rw [module_implTypes_eq_native]
    simp only [Array.getElem?_map, lower_func_at contextRow implementationRow,
      Option.map_some, Option.getD_some]
  rw [typeRow]
  exact accepted_function_computed_summaryClosed accepted contextRow implementationRow

theorem lowerGlobal_summaryClosed (module : Core.Module) (global : Core.Global) (effect : Core.Eff) :
    (lowerGlobal module global).init.summaryClosed effect = .ok () := rfl

#print axioms accepted_module_function_summaryClosed
#print axioms lowerGlobal_summaryClosed

end Goose.Lower.Validation.SummaryPreservation
