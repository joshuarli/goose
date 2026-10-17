import Goose.Proofs.ConstructionExecutionProtocolDestination
import Goose.Proofs.ConstructionExecutionProtocolReceivingRenewMetadataProgress

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

theorem reservationLifecycleInvariant_restore_completed_owner (state : ConstructionState)
    (id : DestinationId) (parent : PendingDestination) (count : Nat) (child : DestinationId)
    (present : state.destinations[id]? = some parent)
    (suspended : parent.progress = .suspended count child)
    (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant {state with
      destinations := state.destinations.set! id {parent with progress := .built count}} := by
  constructor
  · apply destinationLifecycleInvariant_replace_silent state id parent
      {parent with progress := .built count} state.storage present rfl rfl rfl rfl
    · intro phase matched
      cases phase <;> simpa only [DestinationTracePhase.matchesDestination,
        DestinationTracePhase.matchesProgress, suspended] using matched
    · exact valid.1
  · apply destinationReservationStateValid_frame state _
    · apply reservationMetadataFrame_replace_progress state id parent _ present
      intro stable
      simp only [suspended, ReservationStableProgress] at stable
    · exact valid.2

end Goose.Proofs.ConstructionExecutionProtocol
