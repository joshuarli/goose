import Goose.Proofs.ConstructionExecutionOwnershipSuccessorPaths
import Goose.Proofs.ConstructionExecutionOwnershipSourcePrimitives

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Proofs.ConstructionExecutionProtocol

theorem constructionPrimitive_successorRoles_of_sourceExtension {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (valid : ReservationLifecycleInvariant state) (successors : DestinationSuccessorsValid state)
    (roles : LiveFreshReservationSuccessorRoles state)
    (source : OwnershipSourceExtension state (action state).finalState) :
    LiveFreshReservationSuccessorRoles (action state).finalState := by
  have metadata := constructionPrimitive_reservation_frame action primitive state valid.1
  apply liveFreshReservationSuccessorRoles_sourceExtension state _ valid successors source
    (constructionPrimitive_successorMap action primitive state) _ roles
  intro token incoming reserved snapshot present
  simpa only [metadata.tickets] using present

theorem constructionPrimitive_successorRoles_or_landing {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (valid : ReservationLifecycleInvariant state) (successors : DestinationSuccessorsValid state)
    (roles : LiveFreshReservationSuccessorRoles state) :
    LiveFreshReservationSuccessorRoles (action state).finalState ∨ ∃ id, HEq action (landExitReplacement id) := by
  rcases constructionPrimitive_source_or_landing action primitive state valid.1 with source | landing
  · exact Or.inl (constructionPrimitive_successorRoles_of_sourceExtension action primitive state valid successors roles source)
  · exact Or.inr landing

end Goose.Proofs.ConstructionExecutionOwnership
