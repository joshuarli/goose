import Goose.Proofs.ConstructionExitBorrowedWorld
import Goose.Proofs.ConstructionExecutionProtocolReservationRearm

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem waiting_update_active_preimage (state : ConstructionState) (token incoming index : Nat)
    (role : ExitReservationRole) (source selected : Nat) (snapshot : PendingDestination)
    (ticket : (state.exitReservations.set! token (.waiting incoming))[index]? = some (.active role source selected snapshot)) :
    state.exitReservations[index]? = some (.active role source selected snapshot) := by
  by_cases same : token = index
  · subst index
    by_cases inside : token < state.exitReservations.size
    · simp [Array.set!_eq_setIfInBounds, inside] at ticket
    · simp [Array.set!_eq_setIfInBounds, inside] at ticket ⊢
  · simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, same] using ticket

theorem waiting_update_lifecycle (state : ConstructionState) (receipt : BorrowedWaitingExitReservation)
    (stage : NamedReservationStage) (incoming selected current : Nat) (snapshot row : PendingDestination)
    (ticket : state.exitReservations[receipt.token]? = some (.active (.named stage) incoming selected snapshot))
    (resolved : destinationCurrent state receipt.incoming = .ok current)
    (present : state.destinations[current]? = some row)
    (lifecycle : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant { state with exitReservations := state.exitReservations.set! receipt.token (.waiting receipt.incoming) } := by
  let restored := { state with exitReservations := state.exitReservations.set! receipt.token .restored }
  have cancelled : cancelExitReservation receipt.token [] state = .ok () restored := by
    simp [cancelExitReservation, ConstructionM.get, ticket, bind, ConstructionM.set, restored]
  have retained := cancelExitReservation_lifecycle receipt.token [] state lifecycle
  rw [cancelled] at retained
  have inside := (Array.getElem?_eq_some_iff.mp ticket).1
  have restoredTicket : restored.exitReservations[receipt.token]? = some .restored := by
    simp only [restored, Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_self_of_lt inside
  have restoredCurrent : destinationCurrent restored receipt.incoming = .ok current :=
    (destinationCurrent_congr_tables state restored rfl rfl receipt.incoming).trans resolved
  have rearmed := rearmExitReservation_lifecycle receipt restored retained
  have rearm : rearmExitReservation receipt restored = .ok ()
      { state with exitReservations := state.exitReservations.set! receipt.token (.waiting receipt.incoming) } := by
    simp only [rearmExitReservation, ConstructionM.get, bind, restoredTicket, restoredCurrent,
      lookupDestination_result, ConstructionM.set, pure]
    simp [restored, present, Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds]
  simpa only [rearm, ConstructionResult.finalState] using rearmed

theorem waiting_update_source_roles (state : ConstructionState) (token incoming : Nat)
    (valid : OwnershipSourceState state) :
    let after := { state with exitReservations := state.exitReservations.set! token (.waiting incoming) }
    LiveFreshReservationSuccessorRoles after ∧ DestinationSuccessorKeysInactive after ∧ ResumptionReservationRoles after := by
  let after := { state with exitReservations := state.exitReservations.set! token (.waiting incoming) }
  refine ⟨?_, valid.inactiveKeys, ?_⟩
  · intro index source selected node snapshot row found path present
    have old := waiting_update_active_preimage state token incoming index .fresh source selected snapshot found
    have oldPath := DestinationSuccessorPath.congr (before := after) (after := state) rfl path
    exact valid.aliases index source selected node snapshot row old oldPath present
  · intro key saved present index source selected snapshot found current
    have old := waiting_update_active_preimage state token incoming index .fresh source selected snapshot found
    have oldCurrent := (destinationCurrent_congr_tables state after rfl rfl selected).symm.trans current
    exact valid.resumptionRoles key saved present index source selected snapshot old oldCurrent

theorem waiting_update_source (state : ConstructionState) (receipt : BorrowedWaitingExitReservation)
    (stage : NamedReservationStage) (incoming selected current : Nat) (snapshot row : PendingDestination)
    (ticket : state.exitReservations[receipt.token]? = some (.active (.named stage) incoming selected snapshot))
    (resolved : destinationCurrent state receipt.incoming = .ok current)
    (present : state.destinations[current]? = some row)
    (valid : OwnershipSourceState state) :
    OwnershipSourceState { state with exitReservations := state.exitReservations.set! receipt.token (.waiting receipt.incoming) } := by
  let after := { state with exitReservations := state.exitReservations.set! receipt.token (.waiting receipt.incoming) }
  have lifecycle := waiting_update_lifecycle state receipt stage incoming selected current snapshot row ticket resolved present valid.structural.1.1
  have roles := waiting_update_source_roles state receipt.token receipt.incoming valid
  have links : ConstructionOwnershipLinks after := by
    refine ⟨lifecycle.1, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · exact valid.structural.1.2.1.2.1
    · intro index oldIncoming oldSelected oldSnapshot found
      exact valid.structural.1.2.1.2.2.1.1 index oldIncoming oldSelected oldSnapshot
        (waiting_update_active_preimage state receipt.token receipt.incoming index .fresh oldIncoming oldSelected oldSnapshot found)
    · exact valid.structural.1.2.1.2.2.1.2
    · intro index oldIncoming oldSelected oldSnapshot found
      exact valid.structural.1.2.1.2.2.2.1 index oldIncoming oldSelected oldSnapshot
        (waiting_update_active_preimage state receipt.token receipt.incoming index .fresh oldIncoming oldSelected oldSnapshot found)
    · intro index oldIncoming oldSelected oldSnapshot currentRow found
      exact valid.structural.1.2.1.2.2.2.2.1 index oldIncoming oldSelected oldSnapshot currentRow
        (waiting_update_active_preimage state receipt.token receipt.incoming index .fresh oldIncoming oldSelected oldSnapshot found)
    · intro index oldIncoming oldSelected oldSnapshot found
      exact valid.structural.1.2.1.2.2.2.2.2.1 index oldIncoming oldSelected oldSnapshot
        (waiting_update_active_preimage state receipt.token receipt.incoming index .fresh oldIncoming oldSelected oldSnapshot found)
    · exact valid.structural.1.2.1.2.2.2.2.2.2
  have authority : SupportedReplacementAuthority after := by
    intro id parent selectedRow found use supported
    exact valid.structural.1.2.2.1 id parent selectedRow found use
      (replacementSupported_congr_destinations after state rfl id supported)
  have backing : ResumptionBackingSources after := valid.structural.1.2.2.2.1
  have unsupported : UnsupportedResumptionKeys after := by
    intro id saved found supported
    exact valid.structural.1.2.2.2.2.1 id saved found
      (replacementSupported_congr_destinations after state rfl id supported)
  have currentRoles : LiveFreshReservationRoles after := liveFreshReservationSuccessorRoles_current after roles.1
  have rawRoles : LiveFreshReservationRawRoles after := liveFreshReservationSuccessorRoles_raw after roles.1
  exact ⟨⟨⟨lifecycle, links, authority, backing, unsupported, currentRoles⟩, valid.structural.2.1, rawRoles⟩,
    roles.1, roles.2.1, roles.2.2⟩

#print axioms waiting_update_source
#print axioms waiting_update_lifecycle
#print axioms waiting_update_source_roles

end Goose.Proofs.ConstructionAcceptedExecution
