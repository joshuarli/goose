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
        parent.capability.id = before.capability.id ∧ parent.backing = before.backing ∧
        parent.use = before.use ∧
        (∀ (phase : DestinationTracePhase), phase.matchesDestination before → phase.matchesDestination parent) ∧ ¬ ReservationStableProgress before.progress ∧ parentId < id)
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
      obtain ⟨before, parentPresent, parentCapability, parentBacking, parentUse, parentTransition, parentMutable, earlier⟩ := parentValid parentId parent rfl
      have different : id ≠ parentId := (Nat.ne_of_lt earlier).symm
      have parentInside := (Array.getElem?_eq_some_iff.mp parentPresent).choose
      have parentAfter : (state.destinations.set! id updated)[parentId]? = some before := by
        simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different] using parentPresent
      have parentChanged : ReservationMetadataFrame
          { state with destinations := state.destinations.set! id updated }
          { state with destinations := (state.destinations.set! id updated).set! parentId parent } := by
        simpa only [List.append_nil] using reservationMetadataFrame_replace_mutable
          { state with destinations := state.destinations.set! id updated } parentId before parent
          state.storage [] parentAfter (Nat.le_refl _) parentMutable (by intro queried different; rfl)
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
        parent.capability.id = before.capability.id ∧ parent.backing = before.backing ∧
        parent.use = before.use ∧
        (∀ (phase : DestinationTracePhase), phase.matchesDestination before → phase.matchesDestination parent) ∧ ¬ ReservationStableProgress before.progress ∧ parentId < old)
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
                  parent.capability.id = before.capability.id ∧ parent.backing = before.backing ∧
                  parent.use = before.use ∧
                  (∀ (phase : DestinationTracePhase), phase.matchesDestination before → phase.matchesDestination parent) ∧ ¬ ReservationStableProgress before.progress ∧ parentId < id := by
              intro parentId parent selected
              obtain ⟨before, found, capability, backing, use, transition, mutable, earlier⟩ := parentValid parentId parent selected
              refine ⟨before, ?_, capability, backing, use, transition, mutable, Nat.lt_trans earlier orderedIds⟩
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

private abbrev metadataCompletedStep (id old : DestinationId) (count : Nat)
    (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination)) : ConstructionM Unit :=
  (fun {left right : ConstructionM Unit} (_ : left = right) => left)
    (landCompletedReplacement_transition id old count replacement superseded parentUpdate)

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

private theorem metadataCompletedStep_frame (state : ConstructionState) (id old : DestinationId) (count : Nat)
    (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination))
    (present : state.destinations[id]? = some replacement)
    (progress : replacement.progress = .built count)
    (owner : match superseded.use with
      | .receiver => True
      | .child parent | .replacement parent => parent < id)
    (parentValid : ∀ parentId parent, parentUpdate = some (parentId, parent) →
      ∃ before, state.destinations[parentId]? = some before ∧
        parent.capability.id = before.capability.id ∧ parent.backing = before.backing ∧
        parent.use = before.use ∧
        (∀ (phase : DestinationTracePhase), phase.matchesDestination before → phase.matchesDestination parent) ∧ ¬ ReservationStableProgress before.progress ∧ parentId < old)
    (orderedIds : old < id)
    (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (metadataCompletedStep id old count replacement superseded parentUpdate state).finalState := by
  have expected := landing_completion_metadata protectedStep protectedStep_nil protectedStep_cons
    state id old count replacement superseded parentUpdate present progress owner parentValid orderedIds valid
  simp only [metadataCompletedStep, landCompletedReplacement_transition, landingCompletion,
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

set_option maxHeartbeats 2000000 in
theorem landExitReplacement_reservation_frame (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (landExitReplacement id state).finalState := by
  simp only [landExitReplacement, lookupDestination, lookupDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some replacement =>
      simp only [present]
      cases use : replacement.use <;> try simp only [use] <;> try exact .refl state
      case replacement old =>
        cases progress : replacement.progress <;> try simp only [progress] <;> try exact .refl state
        case built count =>
          simp only [pure, bind, lookupDestination, lookupDestination_result]
          have orderedIds : old < id := by simpa only [use] using valid.2.2.2 id replacement present
          cases oldPresent : state.destinations[old]? with
          | none => exact .refl state
          | some superseded =>
              simp only [oldPresent, bind]
              have owner : match superseded.use with
                  | .receiver => True
                  | .child parent | .replacement parent => parent < id := by
                have prior := valid.2.2.2 old superseded oldPresent
                cases oldUse : superseded.use with
                | receiver => trivial
                | child parent | replacement parent =>
                    exact Nat.lt_trans (by simpa only [oldUse] using prior) orderedIds
              have finishNone := metadataCompletedStep_frame state id old count replacement superseded none
                present progress owner (by intro parentId parent impossible; cases impossible) orderedIds valid
              have finishChild : ∀ parentId parent parentCount,
                  superseded.use = .child parentId → state.destinations[parentId]? = some parent →
                  parent.progress = .suspended parentCount old →
                  ReservationMetadataFrame state (metadataCompletedStep id old count replacement superseded
                    (some (parentId, { parent with progress := .suspended parentCount id })) state).finalState := by
                intro parentId parent parentCount oldUse parentPresent parentProgress
                apply metadataCompletedStep_frame state id old count replacement superseded _ present progress owner
                · intro index updated selected
                  cases selected
                  refine ⟨parent, parentPresent, rfl, rfl, rfl, ?_, ?_, ?_⟩
                  · intro phase matched
                    cases phase <;> simp_all [DestinationTracePhase.matchesDestination, DestinationTracePhase.matchesProgress]
                  · simp [parentProgress, ReservationStableProgress]
                  · simpa only [oldUse] using valid.2.2.2 old superseded oldPresent
                · exact orderedIds
                · exact valid
              have finishUse : ReservationMetadataFrame state (((do
                  let parentUpdate ← match superseded.use with
                    | .receiver => pure none
                    | .child parentId => do
                        let parent ← lookupDestination parentId
                        match parent.progress with
                        | .suspended parentCount expected =>
                            if expected != old then ConstructionM.fail .ownership
                            pure (some (parentId, { parent with progress := .suspended parentCount id }))
                        | _ => ConstructionM.fail .protocol
                    | .replacement _ => ConstructionM.fail .protocol
                  metadataCompletedStep id old count replacement superseded parentUpdate) : ConstructionM Unit) state).finalState := by
                cases oldUse : superseded.use with
                | receiver => exact finishNone
                | replacement prior => exact .refl state
                | child parentId =>
                    simp only [lookupDestination, lookupDestination_result, bind]
                    cases parentPresent : state.destinations[parentId]? with
                    | none => exact .refl state
                    | some parent =>
                        simp only [parentPresent, bind]
                        cases parentProgress : parent.progress <;>
                          try simp only [parentProgress] <;> try exact .refl state
                        case suspended parentCount expected =>
                          by_cases expectedEq : expected = old
                          · subst expected
                            simpa only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, bind] using
                              finishChild parentId parent parentCount oldUse parentPresent parentProgress
                          · simp [expectedEq, ConstructionM.fail, bind, ConstructionResult.finalState]
                            exact .refl state
              cases oldProgress : superseded.progress <;>
                try simp only [oldProgress] <;> try exact .refl state
              all_goals
                split
                · exact .refl state
                · have expected := finishUse
                  simp only [lookupDestination, lookupDestination_result, metadataCompletedStep, bind, pure,
                    ConstructionM.fail] at expected ⊢
                  cases oldUse : superseded.use with
                  | receiver => simpa only [oldUse] using expected
                  | replacement prior => simpa only [oldUse] using expected
                  | child parentId =>
                      simp only [oldUse] at expected ⊢
                      cases parentPresent : state.destinations[parentId]? with
                      | none => exact .refl state
                      | some parent =>
                          simp only [parentPresent] at expected ⊢
                          cases parentProgress : parent.progress <;>
                            simp only [parentProgress] at expected ⊢
                          all_goals exact expected

#print axioms landExitReplacement_reservation_frame

end Goose.Proofs.ConstructionExecutionProtocol
