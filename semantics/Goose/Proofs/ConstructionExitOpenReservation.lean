import Goose.Proofs.ConstructionExecutionProtocolReservationCombinators
import Goose.Proofs.ConstructionExitReplacementOpen

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionProtocol

theorem reserve_open_receiver_snapshot (before after : ConstructionState) (incoming selected token count : Nat)
    (row : PendingDestination) (present : before.destinations[incoming]? = some row)
    (opened : row.progress = .open (count + 1))
    (current : destinationCurrent before incoming = .ok incoming)
    (reserved : reserveExitDestination incoming .newValue before = .ok (token, selected) after) :
    after.destinations[incoming]? = some { row with progress := .exiting (count + 1) selected } ∧
      after.exitReservations[token]? = some (.active .fresh incoming selected row) := by
  have renewal : renewReceivingDestination incoming before = .ok incoming before := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, present, opened]
  have frontier : exitFrontierAction (before.destinations.size + 1) incoming before = .ok incoming before :=
    exitFrontier_open before.destinations.size incoming (count + 1) before row present opened
  rw [reserveExitDestination_equation] at reserved
  simp only [show (ExitSource.newValue == ExitSource.namedResult) = false from rfl,
    Bool.false_eq_true, ↓reduceIte, renewal, bind, ConstructionM.get, frontier,
    reserveLookupStep, lookupDestination_result, present, opened, Bool.false_or] at reserved
  cases replacement : openExitReplacement incoming before with
  | fault reason state => simp only [replacement] at reserved; cases reserved
  | ok picked state =>
    simp only [replacement, ConstructionM.get, ConstructionM.set, bind, pure, ConstructionResult.ok.injEq] at reserved
    obtain ⟨samePair, rfl⟩ := reserved
    cases samePair
    exact ⟨open_replacement_parent_exact before state incoming selected (count + 1) row present opened replacement, by simp⟩

#print axioms reserve_open_receiver_snapshot

end Goose.Proofs.ConstructionAcceptedExecution
