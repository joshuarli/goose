import Goose.Proofs.ConstructionAcceptedElementWrite
import Goose.Proofs.ExitExecutionCleanupStoragePrefixes

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ExitExecution

theorem writeElement_storage_prefix (before after : ConstructionState) (id : Nat)
    (payload : ByteArray) (row : PendingDestination) (storage : ReceivingStorage)
    (limit : Nat → Nat) (present : before.destinations[id]? = some row)
    (stored : before.storage[row.storage]? = some storage)
    (bounded : row.writeEnd ≤ storage.bytes.size) (cutoff : limit row.storage ≤ row.writeEnd)
    (executed : writeElement id payload before = .ok () after) :
    StoragePrefixesEqual limit before.storage after.storage := by
  have transition := writeElement_transition id payload before
  rw [executed] at transition
  cases transition with
  | written destination actual count found bytes opened =>
    have sameRow := Option.some.inj (found.symm.trans present)
    subst destination
    have sameStorage := Option.some.inj (bytes.symm.trans stored)
    subst actual
    have inside := (Array.getElem?_eq_some_iff.mp stored).1
    have prefixSize : (storage.bytes.extract 0 row.writeEnd).size = row.writeEnd := by
      simp [ByteArray.size_extract, bounded]
    have full : (storage.bytes.extract 0 row.writeEnd ++ payload ++
        storage.bytes.extract (row.writeEnd + payload.size) storage.bytes.size).extract 0 row.writeEnd =
        storage.bytes.extract 0 row.writeEnd := by
      rw [ByteArray.append_assoc]
      exact ByteArray.extract_append_eq_left prefixSize.symm
    have observed := congrArg (fun data => data.extract 0 (limit row.storage)) full
    have prefix' : (storage.bytes.extract 0 row.writeEnd ++ payload ++
        storage.bytes.extract (row.writeEnd + payload.size) storage.bytes.size).extract 0 (limit row.storage) =
        storage.bytes.extract 0 (limit row.storage) := by
      simpa only [ByteArray.extract_extract, Nat.zero_add, Nat.min_eq_left cutoff] using observed
    intro selected
    by_cases same : row.storage = selected
    · subst selected
      simp only [storagePrefixObservation, Array.set!, Array.getElem?_setIfInBounds_self_of_lt inside,
        stored, Option.map_some, prefix']
    · simp only [storagePrefixObservation, Array.set!, Array.getElem?_setIfInBounds_ne same]

theorem backed_byte_write_storage_prefix (layout : LayoutEnv) (before : ExecutionState)
    (after : ConstructionState) (id count : Nat) (payload : ByteArray) (limit : Nat → Nat)
    (ready : OpenDestinationBacking layout before id (.varr (.int .u8)) count)
    (cutoff : limit ready.destination.storage ≤ ready.destination.capability.start)
    (executed : writeElement id payload before.construction = .ok () after) :
    StoragePrefixesEqual limit before.construction.storage after.storage := by
  have monotone := elementsEnd_monotone ready.fuel layout ready.element count ready.storage.bytes
    (destinationPayloadStart ready.destination) ready.destination.writeEnd ready.scan
  have safe : limit ready.destination.storage ≤ ready.destination.writeEnd := by
    unfold destinationPayloadStart at monotone
    omega
  exact writeElement_storage_prefix before.construction after id payload ready.destination ready.storage
    limit ready.present ready.bytes ready.bounded safe executed

#print axioms writeElement_storage_prefix
#print axioms backed_byte_write_storage_prefix

end Goose.Proofs.ConstructionAcceptedExecution
