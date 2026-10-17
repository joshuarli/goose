import Goose.Lower.Validation.ReplacementContentFlowSourceClosure

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem accepted_context_entry_checked {module : Core.Module} {ctx : Context} {impl : Impl} :
    ((lowerContextAt module ctx impl).blocks[0]?).any (fun entry =>
      entry.params.map (·.2) == (lowerContextAt module ctx impl).params.map VTy.data) = true := by
  obtain ⟨entry, row, types⟩ := lowerContext_entry_types module ctx impl
  simp [row, types]

theorem accepted_global_entry_checked {module : Core.Module} {global : Core.Global} :
    ((lowerGlobal module global).init.blocks[0]?).any (fun entry =>
      entry.params.map (·.2) == (lowerGlobal module global).init.params.map VTy.data) = true := by
  obtain ⟨entry, row, types⟩ := lowerGlobal_entry_types module global
  simp [row, types]

theorem accepted_global_checkReturned {module : Core.Module} {index : GlobalId}
    {global : Core.Global} (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global) (state : State) :
    checkReturned (lowerGlobal module global).init state = true := by
  have checked := (Core.Sound.validate_modOk module accepted).glob index global globalRow
  simp [checkReturned, lowerGlobal, checked.ty.2]

theorem accepted_global_checkWrites {module : Core.Module} {global : Core.Global}
    {state : State} (shape : state.Shape (lowerGlobal module global).init) :
    checkWrites (lowerGlobal module global).init state = true := by
  have empty : state.writes = #[] := Array.eq_empty_of_size_eq_zero (by simpa [lowerGlobal] using shape.writes)
  simp [checkWrites, empty]

#print axioms accepted_context_entry_checked
#print axioms accepted_global_entry_checked
#print axioms accepted_global_checkReturned
#print axioms accepted_global_checkWrites

end Goose.Lower.Validation.ReplacementContentFlowSource
