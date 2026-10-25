import Goose.Lower.Validation.ReplacementContentFlowSourceReadySteps

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem initial_contents_ready (func : Func) (types : Array (Option VTy)) (index : Nat) :
    flowAt (start func types).contents index ≠ .pending := by
  have components := congrArg State.contents (start_components func types)
  rw [components]
  cases found : func.params[index]? with
  | none => simp [flowAt, Array.getElem?_mapIdx, found]
  | some type =>
    by_cases reference : type.isRefSlice = true
    · simp [flowAt, Array.getElem?_mapIdx, found, reference]
    · simp [flowAt, Array.getElem?_mapIdx, found, reference]

theorem contents_ready_of_initial_extends {func : Func} {types : Array (Option VTy)} {state : State}
    (growth : (start func types).Extends state) (index : Nat) : flowAt state.contents index ≠ .pending :=
  (growth.contents.values index).ready (initial_contents_ready func types index)

theorem content_ready {func : Func} {state : State} {address : Roots}
    (ready : address ≠ .pending)
    (locals : ∀ atoms, address = .known atoms → ∀ slot, Atom.local slot ∈ atoms → flowAt state.slots slot ≠ .pending)
    (parameters : ∀ index, (func.params[index]?).any Ty.isRefSlice = true → flowAt state.contents index ≠ .pending) :
    content func state address ≠ .pending := by
  apply bind_ready ready
  intro atoms equality atom member
  cases atom with
  | «local» slot => exact locals atoms equality slot member
  | global global => simp
  | contents index => simp
  | param index =>
    by_cases reference : (func.params[index]?).any Ty.isRefSlice = true
    · simpa only [reference, ite_true] using parameters index reference
    · simp [reference]

theorem content_local_ready {func : Func} {state : State} {slot : SlotId}
    (ready : flowAt state.slots slot ≠ .pending) : content func state (.known [.local slot]) ≠ .pending := by
  cases found : flowAt state.slots slot <;> simp_all [content, Roots.bind, Roots.join]

#print axioms initial_contents_ready
#print axioms contents_ready_of_initial_extends
#print axioms content_ready
#print axioms content_local_ready

end Goose.Lower.Validation.ReplacementContentFlowSource
