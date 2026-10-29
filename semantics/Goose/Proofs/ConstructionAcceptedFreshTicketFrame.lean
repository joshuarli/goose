import Goose.Proofs.ConstructionAcceptedFreshBytePending

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

def FreshDestinationFrame.replace_ticket_rebase {before state after : ExecutionState}
    (frame : FreshDestinationFrame before state) (token : Nat) (reservation : ExitReservation)
    (construction : after.construction = { state.construction with
      exitReservations := state.construction.exitReservations.set! token reservation }) :
    let baseline := { after with construction := { before.construction with
      exitReservations := before.construction.exitReservations.set! token reservation } }
    FreshDestinationFrame baseline after := by
  let baseline := { after with construction := { before.construction with
    exitReservations := before.construction.exitReservations.set! token reservation } }
  refine ⟨rfl, frame.row, ?_, frame.receiver, ?_, ?_, ?_⟩
  · simpa only [baseline, construction] using frame.destinations
  · simpa only [baseline, construction] using frame.successors
  · simp only [construction, frame.tickets]
  · intro id storage found
    simpa only [baseline, construction] using frame.storage id storage found

def FreshDestinationFrame.rebase_runtime {before state after : ExecutionState}
    (frame : FreshDestinationFrame before state) (construction : after.construction = state.construction) :
    FreshDestinationFrame { after with construction := before.construction } after := by
  refine ⟨rfl, frame.row, ?_, frame.receiver, ?_, ?_, ?_⟩
  · simpa only [construction] using frame.destinations
  · simpa only [construction] using frame.successors
  · simpa only [construction] using frame.tickets
  · intro id storage found
    simpa only [construction] using frame.storage id storage found

#print axioms FreshDestinationFrame.replace_ticket_rebase
#print axioms FreshDestinationFrame.rebase_runtime
end Goose.Proofs.ConstructionAcceptedExecution
