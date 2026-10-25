import Goose.Construct.Destination

set_option Elab.async false

namespace Goose.Proofs.ConstructionStorage
open Goose.Construct Goose.Core

structure FixedWidthStorageWrite (before after : Array ReceivingStorage)
    (storageId start : Nat) (payload : ByteArray) (original : ReceivingStorage) : Prop where
  present : before[storageId]? = some original
  bounded : start + payload.size ≤ original.bytes.size
  updated : after = before.set! storageId { original with bytes := (original.bytes.extract 0 start ++ payload ++
      original.bytes.extract (start + payload.size) original.bytes.size) }

theorem FixedWidthStorageWrite.storage_count
    (write : FixedWidthStorageWrite before after storageId start payload original) :
    after.size = before.size := by
  rw [write.updated]
  simp

theorem FixedWidthStorageWrite.other_storage
    (write : FixedWidthStorageWrite before after storageId start payload original)
    (different : other ≠ storageId) : after[other]? = before[other]? := by
  rw [write.updated]
  simp [Array.set!_eq_setIfInBounds, Ne.symm different]

theorem FixedWidthStorageWrite.byte_count
    (write : FixedWidthStorageWrite before after storageId start payload original) :
    ∃ current, after[storageId]? = some current ∧
      current.bytes.size = original.bytes.size ∧
      current.publishedCount = original.publishedCount := by
  have inside := (Array.getElem?_eq_some_iff.mp write.present).choose
  rw [write.updated]
  refine ⟨{ original with bytes := (original.bytes.extract 0 start ++ payload ++
      original.bytes.extract (start + payload.size) original.bytes.size) }, ?_, ?_, rfl⟩
  · simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside]
  · have bound := write.bounded
    simp only [ByteArray.size_append, ByteArray.size_extract]
    have startBound : start ≤ original.bytes.size := by omega
    simp only [Nat.min_eq_left startBound, Nat.min_self, Nat.sub_zero]
    omega

set_option maxHeartbeats 800000 in
theorem writeElement_receiver_fixedWidth
    (before after : ConstructionState) (id : DestinationId) (destination : PendingDestination)
    (storage : ReceivingStorage) (payload : ByteArray) (count : Nat)
    (found : before.destinations[id]? = some destination)
    (stored : before.storage[destination.storage]? = some storage)
    (opened : destination.progress = .open count)
    (receiver : destination.use = .receiver)
    (bounded : destination.writeEnd + payload.size ≤ storage.bytes.size)
    (executed : writeElement id payload before = .ok () after) :
    FixedWidthStorageWrite before.storage after.storage destination.storage destination.writeEnd payload storage := by
  have destinationInside := (Array.getElem?_eq_some_iff.mp found).choose
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).choose
  refine ⟨stored, bounded, ?_⟩
  simp only [writeElement, bind, writableDestination_result, found] at executed
  cases allowed : destinationCanWrite before id <;> simp only [allowed, bind] at executed
  · contradiction
  · simp only [opened, lookupStorage_result, stored, bind] at executed
    split at executed
    · contradiction
    · cases layout : (destination.adaptation.map (·.layout)).getD destination.layout <;>
        simp only [layout] at executed
      all_goals
        repeat' first
          | split at executed
          | simp_all only [pure, bind, receiver, replaceStorage_result, replaceDestination_result,
              destinationInside, storageInside, Array.size_set!, ↓reduceIte, ConstructionM.fail,
              emit_result, ConstructionResult.ok.injEq, true_and]
      all_goals first | contradiction | (rw [← executed]; rfl)

end Goose.Proofs.ConstructionStorage
