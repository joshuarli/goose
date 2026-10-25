import Goose.Proofs.ConstructionExecutionOwnershipSuccessorSourceKernel
import Goose.Proofs.ConstructionExecutionOwnershipSuccessorInactive
import Goose.Proofs.OwnershipAmbientResumptionRoles

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Proofs.ConstructionExecutionProtocol

structure OwnershipSourceState (state : ConstructionState) : Prop where
  structural : OwnershipSourceStructural state
  aliases : LiveFreshReservationSuccessorRoles state
  inactiveKeys : DestinationSuccessorKeysInactive state
  resumptionRoles : ResumptionReservationRoles state

theorem initial_ownershipSourceState : OwnershipSourceState .initial :=
  ⟨initial_ownershipSourceStructural, initial_liveFreshReservationSuccessorRoles,
    initial_destinationSuccessorKeysInactive, initial_resumptionReservationRoles⟩

theorem constructionPrimitive_sourceState_of_sourceExtension {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (valid : OwnershipSourceState state)
    (source : OwnershipSourceExtension state (action state).finalState) :
    OwnershipSourceState (action state).finalState := by
  have metadata := constructionPrimitive_reservation_frame action primitive state valid.structural.1.1.1
  have map := constructionPrimitive_successorMap action primitive state
  refine ⟨constructionPrimitive_sourceStructural_of_sourceExtension action primitive state valid.structural source,
    constructionPrimitive_successorRoles_of_sourceExtension action primitive state
      valid.structural.1.1 valid.structural.2.1 valid.aliases source,
    constructionPrimitive_successorKeysInactive action primitive state valid.structural.1.1.1 valid.inactiveKeys, ?_⟩
  apply resumptionReservationRoles_extension state _ valid.structural.1.1 valid.structural.2.1 map
    metadata.destinations metadata.resumptions _ valid.resumptionRoles
  intro token incoming reserved snapshot present
  simpa only [metadata.tickets] using present

theorem constructionPrimitive_sourceState_or_landing {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState) (valid : OwnershipSourceState state) :
    OwnershipSourceState (action state).finalState ∨ ∃ id, HEq action (landExitReplacement id) := by
  rcases constructionPrimitive_source_or_landing action primitive state valid.structural.1.1.1 with source | landing
  · exact Or.inl (constructionPrimitive_sourceState_of_sourceExtension action primitive state valid source)
  · exact Or.inr landing

end Goose.Proofs.ConstructionExecutionOwnership
