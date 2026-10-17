import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsAdaptation
import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsAllocationForward
import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsAttach
import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsLandingExecution
import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsPublish
import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsRelocation
import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsStage
import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsTable
import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsTree
import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsWrites
import Goose.Proofs.ConstructionExecutionProtocolReservationLifecycle

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

theorem constructionPrimitive_ownership_forward_rows {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) (authority : SupportedReplacementAuthority state) :
    OwnershipForwardRowsFrame state (action state).finalState := by
  cases primitive with
  | reserveStorage bytes count => exact ⟨reserveStorage_ownership_rows bytes count state, fun links => links⟩
  | appendStdout bytes => exact ⟨appendStdout_ownership_rows bytes state, fun links => links⟩
  | adaptDestinationType id ty => exact ⟨adaptDestinationType_ownership_rows state id ty,
      adaptDestinationType_forwardLinks state id ty⟩
  | restoreReceivingLayout id layout => exact ⟨restoreReceivingLayout_ownership_rows state id layout,
      restoreReceivingLayout_forwardLinks state id layout⟩
  | removeConstructionHeader id => exact ⟨removeConstructionHeader_ownership_rows id state,
      removeConstructionHeader_forwardLinks id state⟩
  | landExitReplacement id => exact landExitReplacement_ownership_frame id state valid authority
  | abandonPreservingExit id replacement => exact abandonPreservingExit_ownership_frame id replacement state valid.2.1
  | recordCopy source id => exact ⟨recordCopy_ownership_rows source id state, recordCopy_forwardLinks source id state⟩
  | writeElement id bytes => exact ⟨writeElement_ownership_rows id bytes state valid,
      writeElement_forwardLinks id bytes state valid⟩
  | finishDestination id => exact ⟨finishDestination_ownership_rows state id valid,
      finishDestination_forwardLinks state id valid⟩
  | attachChild parent child => exact attachChild_ownership_frame parent child state valid
  | attachExtension parent child => exact attachExtension_ownership_frame parent child state valid
  | attachElementExtension parent child => exact attachElementExtension_ownership_frame parent child state valid
  | publishElementDestination id => exact publishElementDestination_ownership_frame id state valid
  | retireRepeatedSource parent source => exact retireRepeatedSource_ownership_frame parent source state valid
  | truncateConstructionStorage storage start finish count owner retain =>
      exact ⟨truncateConstructionStorage_ownership_rows storage start finish count owner retain state valid,
        truncateConstructionStorage_forwardLinks storage start finish count owner retain state valid⟩
  | prepareNamedBinding id ty => exact ⟨prepareNamedBinding_ownership_rows id ty state valid,
      prepareNamedBinding_forwardLinks id ty state valid⟩
  | fitStagedDestination id => exact fitStagedDestination_ownership_frame id state valid
  | publishOperation ids => exact publishOperation_ownership_frame ids state valid
  | abandonDestination id => exact ⟨abandonDestination_ownership_rows state id, abandonDestination_forwardLinks state id⟩
  | stageDestination id => exact ⟨stageDestination_ownership_rows state id, stageDestination_forwardLinks state id⟩
  | abandonTree id => exact abandonTree_ownership_frame id state valid.2.1
  | adaptConstructionDestination id ty request => exact adaptConstructionDestination_ownership_frame id ty request state valid
  | finishConstructionAdaptation id => exact finishConstructionAdaptation_ownership_frame id state
  | normalizeProducerDestination id ty => exact normalizeProducerDestination_ownership_frame id ty state
  | openDestination storage capability layout known => exact ⟨openDestination_ownership_rows storage capability layout known state valid,
      openDestination_forwardLinks storage capability layout known state valid⟩
  | openDestinationDirect storage capability layout known => exact ⟨openDestinationDirect_ownership_rows storage capability layout known state valid,
      openDestinationDirect_forwardLinks storage capability layout known state valid⟩
  | openChild parent ty layout => exact ⟨openChild_ownership_rows parent ty layout state valid,
      openChild_forwardLinks_all_outcomes state parent ty layout valid⟩
  | openExtension parent request known => exact ⟨openExtension_ownership_rows parent request known state valid,
      openExtension_forwardLinks parent request known state valid⟩
  | openElementExtension parent ty layout known receiver => exact ⟨openElementExtension_ownership_rows parent ty layout known receiver state valid,
      openElementExtension_forwardLinks parent ty layout known receiver state valid⟩
  | openExitReplacement parent => exact ⟨openExitReplacement_ownership_rows parent state valid,
      openExitReplacement_forwardLinks_all_outcomes state parent valid⟩

theorem constructionPrimitive_ownership_links {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (reservation : ReservationLifecycleInvariant state) (links : ConstructionOwnershipLinks state)
    (authority : SupportedReplacementAuthority state) : ConstructionOwnershipLinks (action state).finalState := by
  have frame := constructionPrimitive_ownership_forward_rows action primitive state reservation.1 authority
  exact constructionOwnershipLinks_rows_frame state _ reservation links
    (constructionPrimitive_reservation_frame action primitive state reservation.1) frame.1
    (destinationLifecyclePrimitives.preserves action primitive state reservation.1) (frame.2 links.2.1)


theorem constructionPrimitive_supportedReplacementAuthority {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) (authority : SupportedReplacementAuthority state) :
    SupportedReplacementAuthority (action state).finalState :=
  (constructionPrimitive_ownership_forward_rows action primitive state valid authority).1.authority authority

theorem initial_constructionOwnershipSupportedInvariant :
    ReservationLifecycleInvariant .initial ∧ ConstructionOwnershipLinks .initial ∧
      SupportedReplacementAuthority .initial :=
  ⟨initial_reservation_lifecycle_invariant, initial_constructionOwnershipLinks, initial_supportedReplacementAuthority⟩

theorem constructionOwnershipLinkPrimitives : ConstructionProtocolPrimitives
    (fun state => ReservationLifecycleInvariant state ∧ ConstructionOwnershipLinks state ∧
      SupportedReplacementAuthority state) where
  storageFrame := by
    intro state storage size valid
    have reservation := reservationLifecyclePrimitives.storageFrame state storage size valid.1
    refine ⟨reservation, ?_, supportedReplacementAuthority_congr_destinations state _ rfl valid.2.2⟩
    exact constructionOwnershipLinks_rows_frame state _ valid.1 valid.2.1
      (reservationMetadataFrame_storage state storage (Nat.le_of_eq size.symm))
      (ownershipLinkRowsFrame_same_rows state _ rfl) reservation.1 valid.2.1.2.1
  preserves := by
    intro α action primitive state valid
    exact ⟨reservationLifecyclePrimitives.preserves action primitive state valid.1,
      constructionPrimitive_ownership_links action primitive state valid.1 valid.2.1 valid.2.2,
      constructionPrimitive_supportedReplacementAuthority action primitive state valid.1.1 valid.2.2⟩

end Goose.Proofs.ConstructionExecutionOwnership
