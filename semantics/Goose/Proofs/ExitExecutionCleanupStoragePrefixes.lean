import Goose.Proofs.ExitExecutionCleanupStorageRuntime

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core

def storagePrefixObservation (limit : StorageId → Nat) (id : StorageId)
    (storage : Array ReceivingStorage) : Option (Nat × ByteArray) :=
  storage[id]?.map fun entry => (entry.publishedCount, entry.bytes.extract 0 (limit id))

def StoragePrefixesEqual (limit : StorageId → Nat)
    (before after : Array ReceivingStorage) : Prop :=
  ∀ id, storagePrefixObservation limit id after = storagePrefixObservation limit id before

theorem CleanupStorageTrace.size {cuts : List CleanupStorageBoundary}
    {before after : Array ReceivingStorage} (trace : CleanupStorageTrace cuts before after) :
    after.size = before.size := by
  induction trace with
  | refl => rfl
  | cut => simp only [Array.size_set!]
  | rewrite => simp only [Array.size_set!]
  | append left right first second => exact second.trans first

theorem CleanupStorageTrace.prefixes {cuts : List CleanupStorageBoundary}
    {before after : Array ReceivingStorage} (trace : CleanupStorageTrace cuts before after)
    (limit : StorageId → Nat)
    (retained : ∀ cut ∈ cuts, limit cut.storage ≤ cut.retainedEnd) :
    StoragePrefixesEqual limit before after := by
  induction trace with
  | refl => intro id; rfl
  | cut storage id previous finish present =>
      intro selected
      by_cases same : id = selected
      · subst selected
        obtain ⟨bounded, found⟩ := Array.getElem?_eq_some_iff.mp present
        have cutoff := retained ⟨id, finish⟩ (by simp)
        simp only [storagePrefixObservation, Array.set!,
          Array.getElem?_setIfInBounds_self_of_lt bounded, present, Option.map_some,
          ByteArray.extract_extract, Nat.zero_add, Nat.min_eq_left cutoff]
      · simp only [storagePrefixObservation, Array.set!,
          Array.getElem?_setIfInBounds_ne same]
  | rewrite storage id previous current finish present count bytes =>
      intro selected
      by_cases same : id = selected
      · subst selected
        obtain ⟨bounded, found⟩ := Array.getElem?_eq_some_iff.mp present
        have cutoff := retained ⟨id, finish⟩ (by simp)
        have inside : current.bytes.extract 0 (limit id) = previous.bytes.extract 0 (limit id) := by
          have observed := congrArg (fun data => data.extract 0 (limit id)) bytes
          simpa only [ByteArray.extract_extract, Nat.zero_add, Nat.min_eq_left cutoff] using observed
        simp only [storagePrefixObservation, Array.set!,
          Array.getElem?_setIfInBounds_self_of_lt bounded, present, Option.map_some,
          count, inside]
      · simp only [storagePrefixObservation, Array.set!,
          Array.getElem?_setIfInBounds_ne same]
  | @append first second before middle after left right ihLeft ihRight =>
      have leftSafe : ∀ cut ∈ first, limit cut.storage ≤ cut.retainedEnd := by
        intro cut member
        exact retained cut (List.mem_append_left _ member)
      have rightSafe : ∀ cut ∈ second, limit cut.storage ≤ cut.retainedEnd := by
        intro cut member
        exact retained cut (List.mem_append_right _ member)
      intro id
      exact (ihRight rightSafe id).trans (ihLeft leftSafe id)

theorem CleanupStorageTrace.untouched {cuts : List CleanupStorageBoundary}
    {before after : Array ReceivingStorage} (trace : CleanupStorageTrace cuts before after)
    (id : StorageId) (outside : ∀ cut ∈ cuts, cut.storage ≠ id) :
    after[id]? = before[id]? := by
  induction trace with
  | refl => rfl
  | cut storage selected previous finish present =>
      exact Array.getElem?_setIfInBounds_ne (outside ⟨selected, finish⟩ (by simp))
  | rewrite storage selected previous current finish present count bytes =>
      exact Array.getElem?_setIfInBounds_ne (outside ⟨selected, finish⟩ (by simp))
  | append left right first second =>
      exact (second (fun cut member => outside cut (List.mem_append_right _ member))).trans
        (first (fun cut member => outside cut (List.mem_append_left _ member)))

theorem CleanupStorageTrace.publishedCounts {cuts : List CleanupStorageBoundary}
    {before after : Array ReceivingStorage} (trace : CleanupStorageTrace cuts before after) :
    ∀ id : StorageId, (after[id]?.map ReceivingStorage.publishedCount) =
      (before[id]?.map ReceivingStorage.publishedCount) := by
  intro id
  have observed := trace.prefixes (fun _ => 0) (fun _ _ => Nat.zero_le _) id
  simpa only [storagePrefixObservation, Option.map_map, Function.comp_def]
    using congrArg (Option.map Prod.fst) observed

end Goose.Proofs.ExitExecution
