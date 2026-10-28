import Goose.Proofs.ConstructionAcceptedBytePublishDirect
import Goose.Proofs.ConstructionExitByteRetention
import Goose.Proofs.ConstructionAcceptedOwnerLineage
import Goose.Proofs.ConstructionAcceptedByteSource
import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsCleanupAncestry

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem publish_direct_packed_row (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (id storageId count : Nat) (row : PendingDestination) (storage : ReceivingStorage)
    (present : before.construction.destinations[id]? = some row)
    (stored : before.construction.storage[storageId]? = some storage)
    (progress : row.progress = .built count) (receiver : row.use = .receiver)
    (backing : row.backing = .direct storageId) (packed : row.layout = .packed)
    (executed : publishCarriers origin [.completed id] before = .ok () after) :
    ∃ published, after.construction.destinations[id]? = some published ∧
      published.progress = .published count ∧ published.use = .receiver := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [publishCarriers, List.mapM_cons, List.mapM_nil, bind, pure, List.filterMap_cons,
    List.filterMap_nil, _root_.id, liftConstruction, publishOperation, ConstructionM.get, bind] at executed
  cases checked : preflightPublication before.construction [id] with
  | error reason => simp [checked, ConstructionM.fail] at executed
  | ok result =>
    cases result
    simp only [checked, List.forIn_cons, List.forIn_nil, bind, pure, publishReady_transition,
      lookupDestination_result, present, progress, receiver, backing, DestinationBacking.receiverStorage,
      lookupStorage_result, stored, packed, replaceStorage_result, replaceDestination_result,
      storageInside, inside, ↓reduceIte, emit_result, ExecutionStep.ok.injEq, true_and] at executed
    subst after
    refine ⟨{ row with progress := .published count, backing := .direct storageId, writeEnd := row.capability.start + (row.writeEnd - row.capability.start) }, ?_, rfl, receiver⟩
    simpa [Array.set!_eq_setIfInBounds, receiver, packed] using Array.getElem?_setIfInBounds_self_of_lt (a := { row with progress := .published count, backing := .direct storageId, writeEnd := row.capability.start + (row.writeEnd - row.capability.start) }) inside

#print axioms publish_direct_packed_row
theorem publish_direct_packed_size (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (id storageId count : Nat) (row : PendingDestination) (storage : ReceivingStorage)
    (present : before.construction.destinations[id]? = some row)
    (stored : before.construction.storage[storageId]? = some storage)
    (progress : row.progress = .built count) (receiver : row.use = .receiver)
    (backing : row.backing = .direct storageId) (packed : row.layout = .packed)
    (executed : publishCarriers origin [.completed id] before = .ok () after) :
    after.construction.destinations.size = before.construction.destinations.size := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [publishCarriers, List.mapM_cons, List.mapM_nil, bind, pure, List.filterMap_cons,
    List.filterMap_nil, _root_.id, liftConstruction, publishOperation, ConstructionM.get, bind] at executed
  cases checked : preflightPublication before.construction [id] with
  | error reason => simp [checked, ConstructionM.fail] at executed
  | ok result =>
    cases result
    simp only [checked, List.forIn_cons, List.forIn_nil, bind, pure, publishReady_transition,
      lookupDestination_result, present, progress, receiver, backing, DestinationBacking.receiverStorage,
      lookupStorage_result, stored, packed, replaceStorage_result, replaceDestination_result,
      storageInside, inside, ↓reduceIte, emit_result, ExecutionStep.ok.injEq, true_and] at executed
    subst after
    simp [Array.set!_eq_setIfInBounds]

#print axioms publish_direct_packed_size
theorem destinationDescendant_receiver (state : ConstructionState) (id ancestor : Nat)
    (row : PendingDestination) (present : state.destinations[id]? = some row)
    (receiver : row.use = .receiver)
    (descendant : destinationDescendant state.destinations ancestor id = true) : ancestor = id := by
  rw [destinationDescendant_walk] at descendant
  cases size : state.destinations.size with
  | zero => simp [size, ancestryWalk] at descendant
  | succ n =>
    by_cases same : id = ancestor
    · exact same.symm
    · simp [size, ancestryWalk, same, present, receiver] at descendant

theorem replacementSupported_preimage_rows (before after : ConstructionState) (id : Nat)
    (rows : ∀ (index : Nat) (row : PendingDestination), after.destinations[index]? = some row →
      ∃ old, before.destinations[index]? = some old ∧ old.use = row.use ∧
        (activeProgress row.progress = true → activeProgress old.progress = true))
    (supported : ReplacementSupported after id) : ReplacementSupported before id := by
  induction supported with
  | active index row found active =>
    obtain ⟨old, present, use, wasActive⟩ := rows index row found
    exact .active index old present (wasActive active)
  | parent index parent row found use supported ih =>
    obtain ⟨old, present, sameUse, wasActive⟩ := rows index row found
    exact .parent index parent old present (sameUse.trans use) ih

theorem published_receiver_not_supported (before after : ConstructionState) (id count : Nat)
    (row published : PendingDestination)
    (beforeFound : before.destinations[id]? = some row) (built : row.progress = .built count)
    (afterFound : after.destinations[id]? = some published) (done : published.progress = .published count)
    (receiver : published.use = .receiver) (oldReceiver : row.use = .receiver)
    (otherRows : ∀ other, other ≠ id → after.destinations[other]? = before.destinations[other]?)
    (authority : SupportedReplacementAuthority before) : ¬ ReplacementSupported after id := by
  have rows : ∀ (index : Nat) (row : PendingDestination), after.destinations[index]? = some row →
      ∃ old, before.destinations[index]? = some old ∧ old.use = row.use ∧
        (activeProgress row.progress = true → activeProgress old.progress = true) := by
    intro index foundRow found
    by_cases same : index = id
    · subst index
      have equal : foundRow = published := Option.some.inj (found.symm.trans afterFound)
      subst foundRow
      refine ⟨row, beforeFound, ?_, ?_⟩
      · rw [receiver]
        exact oldReceiver
      · intro active
        simp [done, activeProgress] at active
    · exact ⟨foundRow, by simpa only [otherRows index same] using found, rfl, fun active => active⟩
  intro supported
  cases supported with
  | active index activeRow found active =>
    have equal : activeRow = published := Option.some.inj (found.symm.trans afterFound)
    subst activeRow
    simp [done, activeProgress] at active
  | parent child parent childRow found use childSupported =>
    have different : child ≠ id := by
      intro same
      subst child
      have equal : childRow = published := Option.some.inj (found.symm.trans afterFound)
      subst childRow
      rw [receiver] at use
      cases use
    have oldFound : before.destinations[child]? = some childRow := by simpa only [otherRows child different] using found
    have oldSupported := replacementSupported_preimage_rows before after child rows childSupported
    obtain ⟨owner, ownerFound, sameBacking, phase⟩ := authority child id childRow oldFound use oldSupported
    have equal : owner = row := Option.some.inj (ownerFound.symm.trans beforeFound)
    subst owner
    rcases phase with ⟨n, eq⟩ | eq | eq <;> simp [built] at eq

theorem publish_direct_packed_anchors (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (ambient : OwnershipAmbient) (id storageId count : Nat) (row : PendingDestination) (storage : ReceivingStorage)
    (source : OwnershipSourceState before.construction)
    (anchors : RetainedReplacementAnchors before.construction (.completed id :: ambient.retained))
    (present : before.construction.destinations[id]? = some row)
    (stored : before.construction.storage[storageId]? = some storage)
    (progress : row.progress = .built count) (receiver : row.use = .receiver)
    (backing : row.backing = .direct storageId) (packed : row.layout = .packed)
    (executed : publishCarriers origin [.completed id] before = .ok () after) :
    RetainedReplacementAnchors after.construction ambient.retained := by
  obtain ⟨outer, otherRows, storages, successors, tickets⟩ :=
    publish_direct_packed_observed origin before after id storageId count row storage present stored progress receiver backing packed executed
  obtain ⟨published, afterFound, done, afterReceiver⟩ :=
    publish_direct_packed_row origin before after id storageId count row storage present stored progress receiver backing packed executed
  have size := publish_direct_packed_size origin before after id storageId count row storage present stored progress receiver backing packed executed
  have history := publishCompleted_ownershipSource origin id before after source.structural.1.1.1 executed
  have uses := source_extension_same_uses before.construction after.construction size history
  have authority : SupportedReplacementAuthority before.construction := source.structural.1.2.2.1
  have notSupported := published_receiver_not_supported before.construction after.construction id count row published
    present progress afterFound done afterReceiver receiver otherRows authority
  have rows : ∀ (index : Nat) (foundRow : PendingDestination), after.construction.destinations[index]? = some foundRow →
      ∃ old, before.construction.destinations[index]? = some old ∧ old.use = foundRow.use ∧
        (activeProgress foundRow.progress = true → activeProgress old.progress = true) := by
    intro index foundRow found
    by_cases same : index = id
    · subst index
      have equal : foundRow = published := Option.some.inj (found.symm.trans afterFound)
      subst foundRow
      refine ⟨row, present, receiver.trans afterReceiver.symm, ?_⟩
      intro active
      simp [done, activeProgress] at active
    · exact ⟨foundRow, by simpa only [otherRows index same] using found, rfl, fun active => active⟩
  intro index foundRow found inactive supported
  have different : index ≠ id := by intro equal; subst index; exact notSupported supported
  have oldFound : before.construction.destinations[index]? = some foundRow := by simpa only [otherRows index different] using found
  have prior := replacementSupported_preimage_rows before.construction after.construction index rows supported
  obtain ⟨retained, member, descendant⟩ := anchors index foundRow oldFound inactive prior
  have choice : retained = id ∨ retained ∈ completedCarrierIds ambient.retained := by
    simpa [completedCarrierIds] using member
  rcases choice with same | old
  · subst retained
    exact False.elim (different (destinationDescendant_receiver before.construction id index row present receiver descendant))
  · exact ⟨retained, old, by
      rw [← destinationDescendant_congr_uses before.construction.destinations after.construction.destinations uses index retained]
      exact descendant⟩

theorem ownershipAmbientBoundaries_noTickets (state : ConstructionState) (ambient : OwnershipAmbient)
    (noTickets : ∀ frame ∈ ambient, frame.tickets = []) : OwnershipAmbientBoundaries state ambient := by
  induction ambient with
  | nil => trivial
  | cons frame ambient ih =>
    have empty : frame.tickets = [] := noTickets frame (by simp)
    refine ⟨?_, ih (fun other member => noTickets other (by simp [member]))⟩
    intro token incoming reserved selected snapshot member
    rw [empty] at member
    cases member

theorem publish_direct_packed_context_general (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (ambient : OwnershipAmbient) (id storageId count : Nat) (row : PendingDestination) (storage : ReceivingStorage)
    (context : OwnershipExecutionContext before (.returned [.completed id] :: ambient))
    (present : before.construction.destinations[id]? = some row)
    (stored : before.construction.storage[storageId]? = some storage)
    (progress : row.progress = .built count) (receiver : row.use = .receiver)
    (backing : row.backing = .direct storageId) (packed : row.layout = .packed)
    (executed : publishCarriers origin [.completed id] before = .ok () after) :
    OwnershipExecutionContext after ambient := by
  obtain ⟨outer, otherRows, storages, successors, tickets⟩ :=
    publish_direct_packed_observed origin before after id storageId count row storage present stored progress receiver backing packed executed
  have size := publish_direct_packed_size origin before after id storageId count row storage present stored progress receiver backing packed executed
  have source := publishCompleted_sourceState origin id before after context.source executed
  have history := publishCompleted_ownershipSource origin id before after context.source.structural.1.1.1 executed
  have oldAnchors : RetainedReplacementAnchors before.construction (.completed id :: ambient.retained) := by
    simpa [OwnershipAmbient.retained, OwnershipAmbientFrame.carriers] using context.retention.anchors
  have anchors := publish_direct_packed_anchors origin before after ambient id storageId count row storage context.source
    oldAnchors present stored progress receiver backing packed executed
  have uses := source_extension_same_uses before.construction after.construction size history
  have boundaries := boundaries_indexing_frame before.construction after.construction ambient size successors tickets uses
    context.retention.boundaries.2
  have retained : OwnershipAmbientInvariant after.construction ambient := ⟨source.structural.1, anchors, boundaries⟩
  have runtimeOld := (ownershipRuntimeFrames_returned before ambient [.completed id]).mp context.runtime
  have runtime : OwnershipRuntimeFrames after ambient := by
    rw [outer]
    exact ⟨runtimeOld.activations, runtimeOld.breaks⟩
  have reservationsOld := (ownershipReservationFrames_returned before.construction ambient [.completed id]).mp context.reservations
  have reservations : OwnershipReservationFrames after.construction ambient := by
    intro token reservation found needs
    apply reservationsOld token reservation
    · simpa only [tickets] using found
    · exact needs
  have boundsOld := (ownershipCapturedReceivingBounds_returned before.construction ambient [.completed id]).mp context.bounds
  have receivingOld : OwnershipCapturedReceivingFrames before.construction ambient := context.receiving.2
  obtain ⟨bounds, receiving⟩ := ownershipCapturedReceivingFrames_sourceExtension before.construction after.construction ambient
    context.source.structural.1.1 context.source.structural.2.1 source.structural.1.1.1.2.2.2 history successors
    (by omega) tickets boundsOld receivingOld
  have identities : OwnershipRuntimeIdentities after := by
    rw [outer]
    exact ⟨context.identities.activations, context.identities.breaks⟩
  exact ⟨source, retained, runtime, reservations, receiving, bounds, identities⟩

theorem publish_direct_packed_context (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (ambient : OwnershipAmbient) (id storageId count : Nat) (row : PendingDestination) (storage : ReceivingStorage)
    (context : OwnershipExecutionContext before (.returned [.completed id] :: ambient))
    (noTickets : ∀ frame ∈ ambient, frame.tickets = [])
    (present : before.construction.destinations[id]? = some row)
    (stored : before.construction.storage[storageId]? = some storage)
    (progress : row.progress = .built count) (receiver : row.use = .receiver)
    (backing : row.backing = .direct storageId) (packed : row.layout = .packed)
    (executed : publishCarriers origin [.completed id] before = .ok () after) :
    OwnershipExecutionContext after ambient := by
  exact publish_direct_packed_context_general origin before after ambient id storageId count row storage context
    present stored progress receiver backing packed executed

#print axioms ownershipAmbientBoundaries_noTickets
#print axioms publish_direct_packed_context_general
#print axioms publish_direct_packed_context
#print axioms publish_direct_packed_anchors
#print axioms replacementSupported_preimage_rows
#print axioms published_receiver_not_supported
#print axioms destinationDescendant_receiver
end Goose.Proofs.ConstructionAcceptedExecution
