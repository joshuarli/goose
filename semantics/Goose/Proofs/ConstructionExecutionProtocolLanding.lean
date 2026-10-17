import Goose.Proofs.ConstructionExecutionProtocolRelocation

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

theorem landReceivingStorage_destination_lifecycle_invariant (id : StorageId)
    (receivingStart payloadStart : Nat) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (landReceivingStorage id receivingStart payloadStart state).finalState := by
  simp only [landReceivingStorage]
  cases present : state.storage[id]? with
  | none => exact valid
  | some storage =>
      simp only [present]
      split
      · apply destinationLifecycleInvariant_storage_frame state _ _ valid
        simp [Array.set!_eq_setIfInBounds]
      · exact valid

end Goose.Proofs.ConstructionExecutionProtocol
