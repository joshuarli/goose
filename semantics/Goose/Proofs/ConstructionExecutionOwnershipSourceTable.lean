import Goose.Proofs.ConstructionExecutionOwnershipLiveFreshRows
import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsTable

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

theorem ownershipSourceExtension_sameRows (before after : ConstructionState)
    (rows : after.destinations = before.destinations) : OwnershipSourceExtension before after := by
  intro id row present
  exact ⟨row, by simpa only [rows] using present, rfl,
    by cases use : row.use <;> simp [OwnershipLinkBacking, use]⟩

theorem reserveStorage_ownership_source (bytes : ByteArray) (count : Nat) (state : ConstructionState) :
    OwnershipSourceExtension state (reserveStorage bytes count state).finalState :=
  ownershipSourceExtension_sameRows state _ rfl

theorem appendStdout_ownership_source (bytes : ByteArray) (state : ConstructionState) :
    OwnershipSourceExtension state (appendStdout bytes state).finalState :=
  ownershipSourceExtension_sameRows state _ rfl

theorem recordCopy_ownership_source (source : CopySource) (id : DestinationId) (state : ConstructionState) :
    OwnershipSourceExtension state (recordCopy source id state).finalState :=
  ownershipSourceExtension_sameRows state _ (recordCopy_keepsOwnershipTable source id state)

end Goose.Proofs.ConstructionExecutionOwnership
