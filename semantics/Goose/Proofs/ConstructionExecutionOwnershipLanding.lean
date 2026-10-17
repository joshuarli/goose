import Goose.Proofs.ConstructionExecutionOwnershipCleanup

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

def landedReplacement (replacement superseded : PendingDestination) (count : Nat) : PendingDestination :=
  { replacement with
    capability := { replacement.capability with start := superseded.capability.start }
    use := superseded.use
    progress := .built count
    writeEnd := replacement.writeEnd - (replacement.capability.start - superseded.capability.start)
    rollbackEnd := superseded.rollbackEnd }

def receiverLandingState (state : ConstructionState) (replacementId supersededId : DestinationId)
    (replacement superseded : PendingDestination) (storage : ReceivingStorage) (count : Nat) : ConstructionState :=
  let cleaned := abandonRowsState (protectedRows state supersededId replacementId) state
  { cleaned with
    storage := cleaned.storage.set! replacement.storage
      (storage.landExit superseded.capability.start replacement.capability.start)
    destinations := cleaned.destinations.set! replacementId (landedReplacement replacement superseded count)
    events := cleaned.events ++
      (if superseded.capability.start < replacement.capability.start then [.relocate replacementId .exitValue] else []) }

set_option maxHeartbeats 1000000 in
theorem landExitReplacement_receiver_exact (state : ConstructionState)
    (replacementId supersededId : DestinationId) (replacement superseded : PendingDestination)
    (storage : ReceivingStorage) (count oldCount : Nat)
    (indexed : DestinationCapabilitiesIndexed state)
    (replacementPresent : state.destinations[replacementId]? = some replacement)
    (supersededPresent : state.destinations[supersededId]? = some superseded)
    (replacementUse : replacement.use = .replacement supersededId)
    (replacementProgress : replacement.progress = .built count)
    (supersededUse : superseded.use = .receiver)
    (supersededProgress : superseded.progress = .exiting oldCount replacementId)
    (sameStorage : superseded.storage = replacement.storage)
    (stored : state.storage[replacement.storage]? = some storage)
    (forward : superseded.capability.start ≤ replacement.capability.start)
    (payloadBounded : replacement.capability.start ≤ storage.bytes.size) :
    landExitReplacement replacementId state = .ok ()
      (receiverLandingState state replacementId supersededId replacement superseded storage count) := by
  have replacementInside := (Array.getElem?_eq_some_iff.mp replacementPresent).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  have bounded := (protectedRows_indexed state supersededId replacementId indexed).1
  have clean := protectedCleanup_exact (protectedRows state supersededId replacementId) state bounded
  have frame := abandonRowsState_frame (protectedRows state supersededId replacementId) state
  simp only [landExitReplacement, lookupDestination_result, bind, replacementPresent,
    replacementUse, replacementProgress, pure, supersededPresent, supersededProgress,
    bne_self_eq_false, sameStorage, Bool.or_self, Bool.false_eq_true, ↓reduceIte, supersededUse,
    landCompletedReplacement_transition, lookupStorage_result, stored,
    Nat.not_lt_of_ge forward, ConstructionM.get]
  change (((_ : List PendingDestination → ConstructionM Unit)
    (protectedRows state supersededId replacementId) >>= _) state) = _
  simp only [bind]
  generalize rowsEq : protectedRows state supersededId replacementId = rows at clean ⊢
  cases rows <;> simp only [protectedCleanup] at clean <;> rw [clean]
  all_goals simp only [bind]
  all_goals simp only [← rowsEq] at *
  all_goals simp only [landReceivingStorage, frame.1, stored, forward, payloadBounded,
    decide_true, Bool.true_and, ↓reduceIte]
  all_goals simp only [replaceDestination_result, frame.2.2.1, replacementInside, ↓reduceIte, emit_result]
  all_goals split <;> simp_all [receiverLandingState, landedReplacement, List.append_assoc, emit_result]

theorem receiverLandingState_exact_events (state : ConstructionState)
    (replacementId supersededId : DestinationId) (replacement superseded : PendingDestination)
    (storage : ReceivingStorage) (count : Nat) :
    (receiverLandingState state replacementId supersededId replacement superseded storage count).events =
      state.events ++ (protectedRows state supersededId replacementId).map
        (fun row => .abandon row.capability.id) ++
      (if superseded.capability.start < replacement.capability.start then
        [.relocate replacementId .exitValue] else []) := by
  simp only [receiverLandingState, (abandonRowsState_frame _ _).2.2.2]

theorem receiverLandingState_replacement (state : ConstructionState)
    (replacementId supersededId : DestinationId) (replacement superseded : PendingDestination)
    (storage : ReceivingStorage) (count : Nat)
    (present : state.destinations[replacementId]? = some replacement) :
    (receiverLandingState state replacementId supersededId replacement superseded storage count).destinations[replacementId]? =
      some (landedReplacement replacement superseded count) := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have size := (abandonRowsState_frame (protectedRows state supersededId replacementId) state).2.2.1
  have insideClean : replacementId <
      (abandonRowsState (protectedRows state supersededId replacementId) state).destinations.size := by
    simpa only [size] using inside
  exact Array.getElem?_setIfInBounds_self_of_lt insideClean

theorem receiverLandingState_cannot_land_again (state : ConstructionState)
    (replacementId supersededId : DestinationId) (replacement superseded : PendingDestination)
    (storage : ReceivingStorage) (count : Nat)
    (present : state.destinations[replacementId]? = some replacement)
    (receiver : superseded.use = .receiver) :
    let final := receiverLandingState state replacementId supersededId replacement superseded storage count
    landExitReplacement replacementId final = .fault .protocol final := by
  have landed := receiverLandingState_replacement state replacementId supersededId replacement superseded storage count present
  simp only [landExitReplacement, lookupDestination_result, bind, landed,
    landedReplacement, receiver]
  rfl

theorem receiverLandingState_superseded_abandoned (state : ConstructionState)
    (replacementId supersededId : DestinationId) (replacement superseded : PendingDestination)
    (storage : ReceivingStorage) (count : Nat)
    (indexed : DestinationCapabilitiesIndexed state)
    (present : state.destinations[supersededId]? = some superseded)
    (different : supersededId ≠ replacementId) (active : activeRow superseded = true) :
    (receiverLandingState state replacementId supersededId replacement superseded storage count).destinations[supersededId]? =
      some { superseded with progress := .abandoned } := by
  have correct := indexed supersededId superseded present
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have member : superseded ∈ state.destinations.toList :=
    Array.mem_toList_iff.mpr (Array.mem_iff_getElem?.mpr ⟨supersededId, present⟩)
  have selected : superseded ∈ protectedRows state supersededId replacementId := by
    apply (protectedRows_exact_selection state supersededId replacementId superseded).mpr
    refine ⟨member, ?_, ?_, active⟩
    · simpa only [correct] using different
    · simpa only [correct] using destinationDescendant_self state supersededId inside
  have cleaned := abandonRowsState_inside (protectedRows state supersededId replacementId) state
    (protectedRows_indexed state supersededId replacementId indexed).1
    (protectedRows_indexed state supersededId replacementId indexed).2 superseded selected
  simp only [receiverLandingState, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_ne different.symm]
  simpa only [correct] using cleaned

end Goose.Proofs.ConstructionExecutionOwnership
