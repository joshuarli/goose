import Goose.Proofs.ConstructionExecutionOwnershipSourceKernel
import Goose.Proofs.ConstructionExecutionOwnershipSourceAllocation
import Goose.Proofs.ConstructionExecutionOwnershipSourceAttach
import Goose.Proofs.ConstructionExecutionOwnershipSourceCleanup
import Goose.Proofs.ConstructionExecutionOwnershipSourceWrites
import Goose.Proofs.ConstructionExecutionOwnershipSourceStage
import Goose.Proofs.ConstructionExecutionOwnershipSourceRelocation
import Goose.Proofs.ConstructionExecutionOwnershipSourcePublish
import Goose.Proofs.ConstructionExecutionOwnershipSourceAdaptation

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Proofs.ConstructionExecutionProtocol

theorem constructionPrimitive_source_or_landing {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    OwnershipSourceExtension state (action state).finalState ∨ ∃ id, HEq action (landExitReplacement id) := by
  cases primitive with
  | reserveStorage bytes count => exact Or.inl (reserveStorage_ownership_source bytes count state)
  | appendStdout bytes => exact Or.inl (appendStdout_ownership_source bytes state)
  | adaptDestinationType id ty => exact Or.inl (adaptDestinationType_ownership_source state id ty)
  | restoreReceivingLayout id layout => exact Or.inl (restoreReceivingLayout_ownership_source state id layout)
  | removeConstructionHeader id => exact Or.inl (removeConstructionHeader_ownership_source id state)
  | landExitReplacement id => exact Or.inr ⟨id, HEq.rfl⟩
  | abandonPreservingExit id replacement => exact Or.inl (abandonPreservingExit_ownership_source id replacement state valid.2.1)
  | recordCopy source id => exact Or.inl (recordCopy_ownership_source source id state)
  | writeElement id bytes => exact Or.inl (writeElement_ownership_source id bytes state valid)
  | finishDestination id => exact Or.inl (finishDestination_ownership_source state id valid)
  | attachChild parent child => exact Or.inl (attachChild_ownership_source parent child state valid)
  | attachExtension parent child => exact Or.inl (attachExtension_ownership_source parent child state valid)
  | attachElementExtension parent child => exact Or.inl (attachElementExtension_ownership_source parent child state valid)
  | publishElementDestination id => exact Or.inl (publishElementDestination_ownership_source id state valid)
  | retireRepeatedSource parent source => exact Or.inl (retireRepeatedSource_ownership_source parent source state valid)
  | truncateConstructionStorage storage start finish count owner retain =>
      exact Or.inl (truncateConstructionStorage_ownership_source storage start finish count owner retain state valid)
  | prepareNamedBinding id ty => exact Or.inl (prepareNamedBinding_ownership_source id ty state valid)
  | fitStagedDestination id => exact Or.inl (fitStagedDestination_ownership_source id state valid)
  | publishOperation ids => exact Or.inl (publishOperation_ownership_source ids state valid)
  | abandonDestination id => exact Or.inl (abandonDestination_ownership_source state id)
  | stageDestination id => exact Or.inl (stageDestination_ownership_source state id)
  | abandonTree id => exact Or.inl (abandonTree_ownership_source id state valid.2.1)
  | adaptConstructionDestination id ty request => exact Or.inl (adaptConstructionDestination_ownership_source id ty request state valid)
  | finishConstructionAdaptation id => exact Or.inl (finishConstructionAdaptation_ownership_source id state)
  | normalizeProducerDestination id ty => exact Or.inl (normalizeProducerDestination_ownership_source id ty state)
  | openDestination storage capability layout known => exact Or.inl (openDestination_ownership_source storage capability layout known state valid)
  | openDestinationDirect storage capability layout known => exact Or.inl (openDestinationDirect_ownership_source storage capability layout known state valid)
  | openChild parent ty layout => exact Or.inl (openChild_ownership_source parent ty layout state valid)
  | openExtension parent request known => exact Or.inl (openExtension_ownership_source parent request known state valid)
  | openElementExtension parent ty layout known receiver => exact Or.inl (openElementExtension_ownership_source parent ty layout known receiver state valid)
  | openExitReplacement parent => exact Or.inl (openExitReplacement_ownership_source parent state valid)

theorem constructionPrimitive_sourceStructural_or_landing {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (valid : OwnershipSourceStructural state) :
    OwnershipSourceStructural (action state).finalState ∨ ∃ id, HEq action (landExitReplacement id) := by
  rcases constructionPrimitive_source_or_landing action primitive state valid.1.1.1 with source | landing
  · exact Or.inl (constructionPrimitive_sourceStructural_of_sourceExtension action primitive state valid source)
  · exact Or.inr landing

end Goose.Proofs.ConstructionExecutionOwnership
