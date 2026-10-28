import Goose.Proofs.ConstructionAcceptedOpenDestination
import Goose.Proofs.ConstructionExitDirectByteLoop

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem adapt_open_receiver_same_type (state : ConstructionState) (id : Nat) (destination : PendingDestination)
    (ty : Ty) (present : state.destinations[id]? = some destination)
    (opened : destination.progress = .open 0) (writable : destinationCanWrite state id = true)
    (logical : destination.capability.logicalType = ty) (constructible : ty.constructible = true) :
    adaptDestinationType id ty state = .ok () state := by
  have compatible : ty.adaptsTo ty = true := by simp only [Ty.adaptsTo, beq_self_eq_true, Bool.true_or]
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have same : { destination with capability := { destination.capability with logicalType := ty } } = destination := by
    rw [← logical]
  have setSame : state.destinations.set! id destination = state.destinations := by
    rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def]
    simp only [inside, ↓reduceDIte]
    have found := (Array.getElem?_eq_some_iff.mp present).2
    rw [← found]
    exact Array.set_getElem_self inside
  simp only [adaptDestinationType, writableDestination_result, present, writable, bind, opened,
    constructible, logical, compatible, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  simp only [opened] at same
  rw [same, replaceDestination_result]
  simp only [inside, ↓reduceIte, setSame]

theorem adapt_open_byte_receiver (config : EvalConfig) (state : ExecutionState) (id : Nat)
    (ready : OpenDestinationBacking config.layout state id (.varr (.int .u8)) 0)
    (receiver : ready.destination.use = .receiver) :
    adaptDestinationType id (.varr (.int .u8)) state.construction = .ok () state.construction := by
  have writable := receiver_destination_writable state.construction id ready.destination ready.present receiver
  exact adapt_open_receiver_same_type state.construction id ready.destination (.varr (.int .u8)) ready.present ready.opened
    writable ready.logicalType rfl

#print axioms adapt_open_receiver_same_type
#print axioms adapt_open_byte_receiver
end Goose.Proofs.ConstructionAcceptedExecution
