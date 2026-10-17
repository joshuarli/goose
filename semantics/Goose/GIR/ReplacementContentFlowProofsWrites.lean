import Goose.GIR.ReplacementContentFlow

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem write_parameter (f : Func) (state : State) (index : Nat) (value : Roots)
    (reference : (f.params[index]?).any Ty.isRefSlice = true) :
    write f state (.known [.param index]) value =
      { state with
        contents := addFlow state.contents index value
        writes := state.writes.set! index
          ((state.writes[index]?.getD (.assigned .unknown)).join (.assigned value)) } := by
  simp [write, reference]

theorem write_parameter_content (f : Func) (state : State) (index : Nat) (value : Roots)
    (reference : (f.params[index]?).any Ty.isRefSlice = true) (bounded : index < state.contents.size) :
    flowAt (write f state (.known [.param index]) value).contents index =
      (flowAt state.contents index).join value := by
  rw [write_parameter f state index value reference]
  simp only [addFlow, flowAt, Array.set!_eq_setIfInBounds, Array.getD_getElem?_setIfInBounds,
    bounded, ite_true]

theorem write_parameter_write (f : Func) (state : State) (index : Nat) (value : Roots)
    (reference : (f.params[index]?).any Ty.isRefSlice = true) (bounded : index < state.writes.size) :
    (write f state (.known [.param index]) value).writes[index]?.getD (.assigned .unknown) =
      (state.writes[index]?.getD (.assigned .unknown)).join (.assigned value) := by
  rw [write_parameter f state index value reference]
  simp only [Array.set!_eq_setIfInBounds, Array.getD_getElem?_setIfInBounds, bounded, ite_true]

#print axioms write_parameter
#print axioms write_parameter_content
#print axioms write_parameter_write

end Goose.GIR.ReplacementContentFlow.Model
