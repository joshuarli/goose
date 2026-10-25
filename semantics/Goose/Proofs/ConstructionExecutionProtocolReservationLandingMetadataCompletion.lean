import Goose.Proofs.ConstructionExecutionProtocolReceivingRenewMetadataProgress
import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataCleanup
import Goose.Proofs.ConstructionExecutionProtocolExitLanding
import Goose.Proofs.ConstructionExecutionProtocolCleanup
import Goose.Proofs.ConstructionExecutionProtocolOwnersAncestry

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

private abbrev lookupStorage (id : StorageId) : ConstructionM ReceivingStorage := fun state =>
  (fun {left right : ConstructionResult ReceivingStorage} (_ : left = right) => left)
    (lookupStorage_result id state)

private abbrev lookupDestination (id : DestinationId) : ConstructionM PendingDestination := fun state =>
  (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left)
    (lookupDestination_result id state)

private abbrev replaceDestination (id : DestinationId) (destination : PendingDestination) :
    ConstructionM Unit := fun state =>
  (fun {left right : ConstructionResult Unit} (_ : left = right) => left)
    (replaceDestination_result id destination state)

private abbrev emit (event : ConstructionEvent) : ConstructionM Unit := fun state =>
  (fun {left right : ConstructionResult Unit} (_ : left = right) => left)
    (emit_result event state)

private theorem landing_update_metadata (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (count nextCount : Nat)
    (present : state.destinations[id]? = some before)
    (beforeProgress : before.progress = .built count) (afterProgress : after.progress = .built nextCount)
    (capability : after.capability.id = before.capability.id)
    (backing : after.backing = before.backing)
    (owner : match after.use with
      | .receiver => True
      | .child parent | .replacement parent => parent < id)
    (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state { state with destinations := state.destinations.set! id after } := by
  simpa only [List.append_nil] using reservationMetadataFrame_replace_mutable state id before after
    state.storage [] present (Nat.le_refl _) (by simp [beforeProgress, ReservationStableProgress])
    (by intro queried different; rfl)

private def landingActive (destination : PendingDestination) : Bool :=
  match destination.progress with
  | .open _ | .suspended _ _ | .built _ | .exiting _ _ => true
  | .published _ | .attached _ | .abandoned | .cancelled | .retired => false

private def landingRows (state : ConstructionState) (old replacement : DestinationId) : List PendingDestination :=
  state.destinations.toList.reverse.filter fun destination =>
    destination.capability.id != replacement &&
      destinationDescendant state.destinations old destination.capability.id && landingActive destination

private theorem landing_rows_valid (state : ConstructionState) (old replacement : DestinationId)
    (valid : DestinationCapabilitiesIndexed state) :
    (∀ destination ∈ landingRows state old replacement,
      state.destinations[destination.capability.id]? = some destination) ∧
    (∀ destination ∈ landingRows state old replacement, ∃ count,
      destination.progress = .open count ∨ destination.progress = .built count ∨
      (∃ child, destination.progress = .suspended count child) ∨
      ∃ replacement, destination.progress = .exiting count replacement) ∧
    (landingRows state old replacement).Pairwise
      (fun first second => first.capability.id ≠ second.capability.id) := by
  refine ⟨?_, ?_, ?_⟩
  · intro destination member
    have member := List.mem_reverse.mp (List.mem_filter.mp member).1
    obtain ⟨index, present⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    simpa only [valid index destination present] using present
  · intro destination member
    have active := (Bool.and_eq_true_iff.mp (List.mem_filter.mp member).2).2
    cases progress : destination.progress <;> simp_all [landingActive]
  · apply List.Pairwise.filter
    apply List.pairwise_reverse.mpr
    have unique : (state.destinations.toList.map (·.capability.id)).Nodup := by
      rw [destination_capability_ids_eq_range state valid]
      exact List.nodup_range
    exact (List.pairwise_map.mp unique).imp (by intro first second different; exact Ne.symm different)

private theorem landing_rows_omit (state : ConstructionState) (old replacement : DestinationId)
    (ordered : DestinationOwnersOrdered state) (index : DestinationId)
    (outside : index = replacement ∨ index < old) :
    ∀ destination ∈ landingRows state old replacement, destination.capability.id ≠ index := by
  intro destination member same
  have selected := (List.mem_filter.mp member).2
  rcases outside with sameId | earlier
  · simp [same, sameId] at selected
  · have absent := destinationDescendant_false_of_lt state ordered old index earlier
    simp [same, absent] at selected

private theorem receiving_rows_frame (id : StorageId) (start payload : Nat) (state : ConstructionState) :
    (landReceivingStorage id start payload state).finalState.destinations = state.destinations := by
  unfold landReceivingStorage
  cases state.storage[id]? <;> simp only
  · rfl
  · split <;> rfl

private theorem landing_relocate_metadata (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (count : Nat)
    (present : state.destinations[id]? = some destination)
    (progress : destination.progress = .built count)
    :
    ReservationMetadataFrame state { state with events := state.events ++ [.relocate id .exitValue] } := by
  apply reservationMetadataFrame_emit_mutable state id destination _ present
  · simp [progress, ReservationStableProgress]
  · intro queried different
    simp [destinationObservations, observeDestination, Ne.symm different]

private theorem landing_updates_metadata (state : ConstructionState) (id : DestinationId)
    (replacement superseded : PendingDestination) (count : Nat)
    (parentUpdate : Option (DestinationId × PendingDestination))
    (present : state.destinations[id]? = some replacement)
    (progress : replacement.progress = .built count)
    (owner : match superseded.use with
      | .receiver => True
      | .child parent | .replacement parent => parent < id)
    (parentValid : ∀ parentId parent, parentUpdate = some (parentId, parent) →
      ∃ before, state.destinations[parentId]? = some before ∧
        ReservationProgressPreserves before.progress parent.progress ∧ parentId < id)
    (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (((do
      replaceDestination id { replacement with
        capability := { replacement.capability with start := superseded.capability.start }
        use := superseded.use
        progress := .built count
        writeEnd := replacement.writeEnd - (replacement.capability.start - superseded.capability.start)
        rollbackEnd := superseded.rollbackEnd }
      if let some (parentId, parent) := parentUpdate then replaceDestination parentId parent
      if superseded.capability.start < replacement.capability.start then
        emit (.relocate id .exitValue)) : ConstructionM Unit) state).finalState := by
  let updated := { replacement with
    capability := { replacement.capability with start := superseded.capability.start }
    use := superseded.use
    progress := .built count
    writeEnd := replacement.writeEnd - (replacement.capability.start - superseded.capability.start)
    rollbackEnd := superseded.rollbackEnd }
  have inside := (Array.getElem?_eq_some_iff.mp present).choose
  have changed := landing_update_metadata state id replacement updated count count present progress rfl rfl rfl owner valid
  have updatedPresent : (state.destinations.set! id updated)[id]? = some updated := by
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside]
  simp only [replaceDestination, replaceDestination_result, inside, ↓reduceIte, bind]
  cases parentUpdate with
  | none =>
      simp only [pure, bind]
      split
      · exact changed.trans (landing_relocate_metadata _ id updated count updatedPresent rfl)
      · exact changed
  | some pair =>
      rcases pair with ⟨parentId, parent⟩
      obtain ⟨before, parentPresent, parentProgressFrame, earlier⟩ := parentValid parentId parent rfl
      have different : id ≠ parentId := (Nat.ne_of_lt earlier).symm
      have parentInside := (Array.getElem?_eq_some_iff.mp parentPresent).choose
      have parentAfter : (state.destinations.set! id updated)[parentId]? = some before := by
        simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different] using parentPresent
      have parentChanged := reservationMetadataFrame_replace_progress
        { state with destinations := state.destinations.set! id updated } parentId before parent parentAfter parentProgressFrame
      have total := changed.trans parentChanged
      have replacementAfter : ((state.destinations.set! id updated).set! parentId parent)[id]? = some updated := by
        simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm different)] using updatedPresent
      simp only [replaceDestination, replaceDestination_result, Array.size_set!, parentInside, ↓reduceIte, bind]
      split
      · exact total.trans (landing_relocate_metadata _ id updated count replacementAfter rfl)
      · exact total

private def landingCompletion (action : List PendingDestination → ConstructionM Unit)
    (id old : DestinationId) (count : Nat) (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination)) : ConstructionM Unit := do
  let _ ← lookupStorage replacement.storage
  if replacement.capability.start < superseded.capability.start then ConstructionM.fail .ownership
  let state ← ConstructionM.get
  action (landingRows state old id)
  landReceivingStorage replacement.storage superseded.capability.start replacement.capability.start
  replaceDestination id { replacement with
    capability := { replacement.capability with start := superseded.capability.start }
    use := superseded.use
    progress := .built count
    writeEnd := replacement.writeEnd - (replacement.capability.start - superseded.capability.start)
    rollbackEnd := superseded.rollbackEnd }
  if let some (parentId, parent) := parentUpdate then replaceDestination parentId parent
  if superseded.capability.start < replacement.capability.start then emit (.relocate id .exitValue)

private theorem receiving_metadata (id : StorageId) (start payload : Nat) (state : ConstructionState) :
    ReservationMetadataFrame state (landReceivingStorage id start payload state).finalState := by
  unfold landReceivingStorage
  cases stored : state.storage[id]? with
  | none => exact .refl state
  | some storage =>
      simp only
      split <;> first
        | exact .refl state
        | exact reservationMetadataFrame_storage state _ (by simp)

private theorem landing_completion_metadata
    (action : List PendingDestination → ConstructionM Unit)
    (nilResult : ∀ state, action [] state = .ok () state)
    (consResult : ∀ destination rest state,
      action (destination :: rest) state =
        if destination.capability.id < state.destinations.size then
          action rest { state with
            destinations := state.destinations.set! destination.capability.id
              { destination with progress := .abandoned }
            events := state.events ++ [.abandon destination.capability.id] }
        else .fault .destination state)
    (state : ConstructionState) (id old : DestinationId) (count : Nat)
    (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination))
    (present : state.destinations[id]? = some replacement)
    (progress : replacement.progress = .built count)
    (owner : match superseded.use with
      | .receiver => True
      | .child parent | .replacement parent => parent < id)
    (parentValid : ∀ parentId parent, parentUpdate = some (parentId, parent) →
      ∃ before, state.destinations[parentId]? = some before ∧
        ReservationProgressPreserves before.progress parent.progress ∧ parentId < old)
    (orderedIds : old < id)
    (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state
      (landingCompletion action id old count replacement superseded parentUpdate state).finalState := by
  simp only [landingCompletion, lookupStorage, lookupStorage_result, bind]
  cases storagePresent : state.storage[replacement.storage]? with
  | none => exact .refl state
  | some storage =>
      simp only [pure, bind]
      by_cases backwards : replacement.capability.start < superseded.capability.start
      · simp only [backwards, ↓reduceIte, ConstructionM.fail, bind, ConstructionResult.finalState]
        exact .refl state
      · simp only [backwards, ↓reduceIte, ConstructionM.get, pure, bind]
        have rowsValid := landing_rows_valid state old id valid.2.1
        have cleanupValid := destinationLifecycleInvariant_abandon_rows action nilResult consResult
          (landingRows state old id) state rowsValid.1 rowsValid.2.1 rowsValid.2.2 valid
        have cleanupMetadata := reservationMetadataFrame_abandon_rows action nilResult consResult (landingRows state old id) state
        have frame := destinationAbandonRows_frame action nilResult consResult (landingRows state old id) state
        have replacementFrame := frame.2.2 id (landing_rows_omit state old id valid.2.2.2 id (Or.inl rfl))
        cases cleaned : action (landingRows state old id) state with
        | fault fault after =>
            simpa only [cleaned, bind, ConstructionResult.finalState] using cleanupMetadata
        | ok value after =>
            simp only [cleaned, ConstructionResult.finalState] at cleanupValid cleanupMetadata frame replacementFrame
            simp only [cleaned, bind]
            have replacementAfter : after.destinations[id]? = some replacement := replacementFrame.trans present
            have parentsAfter : ∀ parentId parent, parentUpdate = some (parentId, parent) →
                ∃ before, after.destinations[parentId]? = some before ∧
        ReservationProgressPreserves before.progress parent.progress ∧ parentId < id := by
              intro parentId parent selected
              obtain ⟨before, found, parentProgressFrame, earlier⟩ := parentValid parentId parent selected
              refine ⟨before, ?_, parentProgressFrame, Nat.lt_trans earlier orderedIds⟩
              exact (frame.2.2 parentId (landing_rows_omit state old id valid.2.2.2 parentId (Or.inr earlier))).trans found
            have receivingValid := landReceivingStorage_destination_lifecycle_invariant replacement.storage
              superseded.capability.start replacement.capability.start after cleanupValid
            have receivingFrame := receiving_rows_frame replacement.storage superseded.capability.start
              replacement.capability.start after
            have receivingMetadata := receiving_metadata replacement.storage superseded.capability.start replacement.capability.start after
            cases received : landReceivingStorage replacement.storage superseded.capability.start
                replacement.capability.start after with
            | fault fault final =>
                simpa only [received, bind, ConstructionResult.finalState] using cleanupMetadata.trans receivingMetadata
            | ok value final =>
                simp only [received, ConstructionResult.finalState] at receivingValid receivingFrame receivingMetadata
                simp only [received, bind]
                apply cleanupMetadata.trans (receivingMetadata.trans ?_)
                apply landing_updates_metadata final id replacement superseded count parentUpdate
                · simpa only [receivingFrame] using replacementAfter
                · exact progress
                · exact owner
                · simpa only [receivingFrame] using parentsAfter
                · exact receivingValid

private abbrev protectedStep (rows : List PendingDestination) : ConstructionM Unit := fun state =>
  match rows with
  | [] => (fun {left right : ConstructionResult Unit} (_ : left = right) => left)
      (protectedAbandonment_nil_transition state)
  | destination :: rest => (fun {left right : ConstructionResult Unit} (_ : left = right) => left)
      (protectedAbandonment_cons_transition destination rest state)

private theorem protectedStep_nil (state : ConstructionState) : protectedStep [] state = .ok () state :=
  protectedAbandonment_nil_transition state

private theorem protectedStep_cons (destination : PendingDestination) (rest : List PendingDestination)
    (state : ConstructionState) :
    protectedStep (destination :: rest) state =
      if destination.capability.id < state.destinations.size then
        protectedStep rest { state with
          destinations := state.destinations.set! destination.capability.id
            { destination with progress := .abandoned }
          events := state.events ++ [.abandon destination.capability.id] }
      else .fault .destination state := by
  cases rest <;> simpa only [protectedStep] using protectedAbandonment_cons_transition destination _ state

theorem completedStep_reservation_frame (state : ConstructionState) (id old : DestinationId) (count : Nat)
    (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination))
    (present : state.destinations[id]? = some replacement)
    (progress : replacement.progress = .built count)
    (owner : match superseded.use with
      | .receiver => True
      | .child parent | .replacement parent => parent < id)
    (parentValid : ∀ parentId parent, parentUpdate = some (parentId, parent) →
      ∃ before, state.destinations[parentId]? = some before ∧
        ReservationProgressPreserves before.progress parent.progress ∧ parentId < old)
    (orderedIds : old < id)
    (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (completedStep id old count replacement superseded parentUpdate state).finalState := by
  have expected := landing_completion_metadata protectedStep protectedStep_nil protectedStep_cons
    state id old count replacement superseded parentUpdate present progress owner parentValid orderedIds valid
  simp only [completedStep, landCompletedReplacement_transition, landingCompletion,
    lookupStorage, lookupStorage_result, bind] at expected ⊢
  cases storagePresent : state.storage[replacement.storage]? with
  | none => exact .refl state
  | some storage =>
      simp only [storagePresent, pure, bind] at expected ⊢
      by_cases backwards : replacement.capability.start < superseded.capability.start
      · simpa only [backwards, ↓reduceIte, ConstructionM.fail, bind, ConstructionResult.finalState] using expected
      · simp only [backwards, ↓reduceIte, ConstructionM.get, bind] at expected ⊢
        change ReservationMetadataFrame state ((protectedStep (landingRows state old id) >>= _) state).finalState at expected
        change ReservationMetadataFrame state (((_ : List PendingDestination → ConstructionM Unit) (landingRows state old id) >>= _) state).finalState
        cases rowsEq : landingRows state old id with
        | nil =>
            cases parentUpdate with
            | none => simpa only [rowsEq, bind, protectedStep, replaceDestination, emit] using expected
            | some pair =>
                rcases pair with ⟨parentId, parent⟩
                simpa only [rowsEq, bind, protectedStep, replaceDestination, emit] using expected
        | cons destination rest =>
            cases parentUpdate with
            | none => simpa only [rowsEq, bind, protectedStep, replaceDestination, emit] using expected
            | some pair =>
                rcases pair with ⟨parentId, parent⟩
                simpa only [rowsEq, bind, protectedStep, replaceDestination, emit] using expected


#print axioms completedStep_reservation_frame

end Goose.Proofs.ConstructionExecutionProtocol
