import Goose.Proofs.ConstructionExecutionOwnershipInactivePrimitives
import Goose.Proofs.ConstructionExecutionOwnershipLiveFreshRows
import Goose.Proofs.ConstructionExecutionOwnershipSuccessorKernel

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Proofs.ConstructionExecutionProtocol

theorem constructionPrimitive_ownershipStructural_of_sourceExtension {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (valid : OwnershipStructural state) (successors : DestinationSuccessorsValid state)
    (source : OwnershipSourceExtension state (action state).finalState) :
    OwnershipStructural (action state).finalState := by
  rcases valid with ⟨lifecycle, links, authority, resumptions, unsupported, roles⟩
  have metadata := constructionPrimitive_reservation_frame action primitive state lifecycle.1
  refine ⟨reservationLifecyclePrimitives.preserves action primitive state lifecycle,
    constructionPrimitive_ownership_links action primitive state lifecycle links authority,
    constructionPrimitive_supportedReplacementAuthority action primitive state lifecycle.1 authority,
    constructionPrimitive_resumptionBackingSources action primitive state lifecycle.1 resumptions,
    constructionPrimitive_unsupportedResumptionKeys action primitive state lifecycle.1 resumptions unsupported,
    ?_⟩
  apply liveFreshReservationRoles_sourceExtension state _ lifecycle successors source
    (constructionPrimitive_successorMap action primitive state) metadata.destinations _ roles
  intro token incoming reserved snapshot present
  simpa only [metadata.tickets] using present

theorem constructionPrimitive_sourceStructural_of_sourceExtension {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (valid : OwnershipSourceStructural state)
    (source : OwnershipSourceExtension state (action state).finalState) :
    OwnershipSourceStructural (action state).finalState := by
  have metadata := constructionPrimitive_reservation_frame action primitive state valid.1.1.1
  refine ⟨constructionPrimitive_ownershipStructural_of_sourceExtension action primitive state valid.1 valid.2.1 source,
    constructionPrimitive_successors action primitive state valid.1.1.1 valid.2.1, ?_⟩
  apply liveFreshReservationRawRoles_sourceExtension state _ valid.1.1 source _ valid.2.2
  intro token incoming reserved snapshot present
  simpa only [metadata.tickets] using present


end Goose.Proofs.ConstructionExecutionOwnership
