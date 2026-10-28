import Goose.Proofs.ConstructionExitDirectCheckpoint
import Goose.Proofs.ConstructionExitDirectSourceRoles

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem recursive_checkpoint_tables :
    recursiveDirectCheckpoint.construction.exitReservations = #[] ∧
    recursiveDirectCheckpoint.construction.destinationSuccessors = [] ∧
    recursiveDirectCheckpoint.construction.destinationResumptions = [] ∧
    recursiveDirectCheckpoint.construction.destinations.size = 2 := by
  cbv

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem recursive_checkpoint_receiver_rows (id : Nat) (row : PendingDestination)
    (present : recursiveDirectCheckpoint.construction.destinations[id]? = some row) :
    row.use = .receiver ∧ row.progress = .open 0 := by
  have bound := (Array.getElem?_eq_some_iff.mp present).1
  rw [recursive_checkpoint_tables.2.2.2] at bound
  have casesId : id = 0 ∨ id = 1 := by omega
  rcases casesId with zero | one <;> subst id <;> cbv at present <;> cases present <;> exact ⟨rfl, rfl⟩

theorem recursive_checkpoint_source : OwnershipSourceState recursiveDirectCheckpoint.construction := by
  let state := recursiveDirectCheckpoint.construction
  have noTickets : state.exitReservations = #[] := recursive_checkpoint_tables.1
  have noSuccessors : state.destinationSuccessors = [] := recursive_checkpoint_tables.2.1
  have noResumptions : state.destinationResumptions = [] := recursive_checkpoint_tables.2.2.1
  have links : ConstructionOwnershipLinks state := by
    refine ⟨recursive_checkpoint_destination_lifecycle, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro id row present
      have phase := (recursive_checkpoint_receiver_rows id row present).2
      simp [DestinationForwardLink, phase]
    · constructor
      · intro token incoming selected snapshot ticket
        simp [noTickets] at ticket
      · intro id snapshot saved
        simp [noResumptions] at saved
    · intro token incoming selected snapshot ticket
      simp [noTickets] at ticket
    · intro token incoming selected snapshot row ticket
      simp [noTickets] at ticket
    · intro token incoming selected snapshot ticket
      simp [noTickets] at ticket
    · intro id snapshot saved
      simp [noResumptions] at saved
  have support : SupportedReplacementAuthority state := by
    intro id parent row present use
    have receiver := (recursive_checkpoint_receiver_rows id row present).1
    rw [receiver] at use
    cases use
  have saved : ResumptionBackingSources state := by
    intro id snapshot found
    simp [noResumptions] at found
  have unsupported : UnsupportedResumptionKeys state := by
    intro id snapshot found
    simp [noResumptions] at found
  have currentRoles : LiveFreshReservationRoles state := by
    intro token incoming selected current snapshot row ticket
    simp [noTickets] at ticket
  have successorValid : DestinationSuccessorsValid state := by
    intro id next edge
    simp [noSuccessors] at edge
  have rawRoles : LiveFreshReservationRawRoles state := by
    intro token incoming selected snapshot row ticket
    simp [noTickets] at ticket
  have roles : LiveFreshReservationSuccessorRoles state := by
    intro token incoming selected node snapshot row ticket
    simp [noTickets] at ticket
  have inactive : DestinationSuccessorKeysInactive state := by
    intro id next edge
    simp [noSuccessors] at edge
  have resumptions : ResumptionReservationRoles state := by
    intro id snapshot found
    simp [noResumptions] at found
  exact ⟨⟨⟨recursive_checkpoint_reservation_lifecycle, links, support, saved, unsupported, currentRoles⟩,
    successorValid, rawRoles⟩, roles, inactive, resumptions⟩

#print axioms recursive_checkpoint_source

end Goose.Proofs.ConstructionAcceptedExecution
