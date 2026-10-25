import Goose.Proofs.ConstructionExecutionOwnershipLinkRows

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

private abbrev ownershipLookupDestination (id : DestinationId) : ConstructionM PendingDestination :=
  fun state => (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left)
    (lookupDestination_result id state)

private abbrev ownershipWritableDestination (id : DestinationId) : ConstructionM PendingDestination :=
  fun state => (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left)
    (writableDestination_result id state)

private abbrev ownershipLookupStorage (id : StorageId) : ConstructionM ReceivingStorage :=
  fun state => (fun {left right : ConstructionResult ReceivingStorage} (_ : left = right) => left)
    (lookupStorage_result id state)

private abbrev ownershipReplaceStorage (id : StorageId) (storage : ReceivingStorage) : ConstructionM Unit :=
  fun state => (fun {left right : ConstructionResult Unit} (_ : left = right) => left)
    (replaceStorage_result id storage state)

private abbrev ownershipEmit (event : ConstructionEvent) : ConstructionM Unit :=
  fun state => (fun {left right : ConstructionResult Unit} (_ : left = right) => left)
    (emit_result event state)

def KeepsOwnershipTable (action : ConstructionM α) : Prop :=
  ∀ state, (action state).finalState.destinations = state.destinations

theorem keepsOwnershipTable_pure (value : α) : KeepsOwnershipTable (pure value) := fun _ => rfl

theorem keepsOwnershipTable_fail (fault : ConstructionFault) :
    KeepsOwnershipTable (ConstructionM.fail (α := α) fault) := fun _ => rfl

theorem keepsOwnershipTable_bind (action : ConstructionM α) (next : α → ConstructionM β)
    (first : KeepsOwnershipTable action) (remaining : ∀ value, KeepsOwnershipTable (next value)) :
    KeepsOwnershipTable (action >>= next) := by
  intro state
  have firstRows := first state
  cases evaluated : action state with
  | fault fault final => simpa only [evaluated, bind, ConstructionResult.finalState] using firstRows
  | ok value middle =>
      simp only [evaluated, ConstructionResult.finalState] at firstRows
      simpa only [bind, evaluated] using (remaining value middle).trans firstRows

theorem keepsOwnershipTable_get : KeepsOwnershipTable ConstructionM.get := fun _ => rfl

theorem keepsOwnershipTable_lookupDestination (id : DestinationId) :
    KeepsOwnershipTable (ownershipLookupDestination id) := by
  intro state
  dsimp only [ownershipLookupDestination]
  rw [lookupDestination_result]
  cases state.destinations[id]? <;> rfl

theorem keepsOwnershipTable_writableDestination (id : DestinationId) :
    KeepsOwnershipTable (ownershipWritableDestination id) := by
  intro state
  dsimp only [ownershipWritableDestination]
  rw [writableDestination_result]
  cases state.destinations[id]? <;> try rfl
  cases destinationCanWrite state id <;> rfl

theorem keepsOwnershipTable_lookupStorage (id : StorageId) :
    KeepsOwnershipTable (ownershipLookupStorage id) := by
  intro state
  dsimp only [ownershipLookupStorage]
  rw [lookupStorage_result]
  cases state.storage[id]? <;> rfl

theorem keepsOwnershipTable_replaceStorage (id : StorageId) (storage : ReceivingStorage) :
    KeepsOwnershipTable (ownershipReplaceStorage id storage) := by
  intro state
  dsimp only [ownershipReplaceStorage]
  rw [replaceStorage_result]
  split <;> rfl

theorem keepsOwnershipTable_emit (event : ConstructionEvent) : KeepsOwnershipTable (ownershipEmit event) := fun _ => rfl

theorem recordCopy_keepsOwnershipTable (source : CopySource) (id : DestinationId) :
    KeepsOwnershipTable (recordCopy source id) := by
  unfold recordCopy
  repeat' first
    | with_reducible exact keepsOwnershipTable_pure _
    | with_reducible exact keepsOwnershipTable_fail _
    | with_reducible exact keepsOwnershipTable_get
    | with_reducible exact keepsOwnershipTable_writableDestination _
    | with_reducible exact keepsOwnershipTable_lookupDestination _
    | with_reducible exact keepsOwnershipTable_lookupStorage _
    | with_reducible exact keepsOwnershipTable_emit _
    | with_reducible apply keepsOwnershipTable_bind
    | dsimp only
    | split
    | intro value

theorem recordCopy_ownership_rows (source : CopySource) (id : DestinationId) (state : ConstructionState) :
    OwnershipLinkRowsFrame state (recordCopy source id state).finalState :=
  ownershipLinkRowsFrame_same_rows state _ (recordCopy_keepsOwnershipTable source id state)

theorem recordCopy_forwardLinks (source : CopySource) (id : DestinationId) (state : ConstructionState)
    (valid : DestinationForwardLinks state) : DestinationForwardLinks (recordCopy source id state).finalState := by
  have same := recordCopy_keepsOwnershipTable source id state
  simpa only [DestinationForwardLinks, DestinationForwardLink, same] using valid

end Goose.Proofs.ConstructionExecutionOwnership
