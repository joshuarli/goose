import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsLanding
import Goose.Proofs.ConstructionExecutionOwnershipReplacementSupport
import Goose.Proofs.ConstructionExecutionProtocolExitLanding

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

private abbrev lookupStorage (id : StorageId) : ConstructionM ReceivingStorage := fun state =>
  (fun {left right : ConstructionResult ReceivingStorage} (_ : left = right) => left) (lookupStorage_result id state)

private abbrev replaceDestination (id : DestinationId) (row : PendingDestination) : ConstructionM Unit := fun state =>
  (fun {left right : ConstructionResult Unit} (_ : left = right) => left) (replaceDestination_result id row state)

private abbrev emit (event : ConstructionEvent) : ConstructionM Unit := fun state =>
  (fun {left right : ConstructionResult Unit} (_ : left = right) => left) (emit_result event state)

private def landingUpdates (id count : Nat) (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination)) : ConstructionM Unit := do
  replaceDestination id { replacement with
    capability := { replacement.capability with start := superseded.capability.start }
    use := superseded.use
    progress := .built count
    writeEnd := replacement.writeEnd - (replacement.capability.start - superseded.capability.start)
    rollbackEnd := superseded.rollbackEnd }
  if let some (parentId, parent) := parentUpdate then replaceDestination parentId parent
  if superseded.capability.start < replacement.capability.start then emit (.relocate id .exitValue)

private def completedFlow (id old count : Nat) (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination)) : ConstructionM Unit := do
  let _ ← lookupStorage replacement.storage
  if replacement.capability.start < superseded.capability.start then ConstructionM.fail .ownership
  let state ← ConstructionM.get
  protectedCleanup (protectedRows state old id)
  landReceivingStorage replacement.storage superseded.capability.start replacement.capability.start
  landingUpdates id count replacement superseded parentUpdate

private theorem completedStep_flow (id old count : Nat) (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination)) :
    completedStep id old count replacement superseded parentUpdate =
      completedFlow id old count replacement superseded parentUpdate := by
  funext state
  simp only [completedStep, landCompletedReplacement_transition, completedFlow, landingUpdates, lookupStorage, lookupStorage_result, bind]
  cases stored : state.storage[replacement.storage]? with
  | none => rfl
  | some storage =>
      simp only [stored, pure, bind]
      by_cases backwards : replacement.capability.start < superseded.capability.start
      · simp only [backwards, ↓reduceIte, ConstructionM.fail, bind]
      · simp only [backwards, ↓reduceIte, ConstructionM.get, bind]
        change ((_ : List PendingDestination → ConstructionM Unit) (protectedRows state old id) >>= _) state =
          (protectedCleanup (protectedRows state old id) >>= _) state
        cases rowsEq : protectedRows state old id <;> cases parentUpdate
        all_goals simp only [rowsEq, protectedCleanup, replaceDestination, emit, bind]

private theorem protectedRows_current (state : ConstructionState) (old id : DestinationId)
    (indexed : DestinationCapabilitiesIndexed state) :
    ∀ row ∈ protectedRows state old id, state.destinations[row.capability.id]? = some row := by
  intro row member
  have original := (protectedRows_exact_selection state old id row).mp member
  obtain ⟨index, found⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp original.1)
  simpa only [indexed index row found] using found

private theorem protectedRows_omit (state : ConstructionState) (old id index : DestinationId)
    (ordered : DestinationOwnersOrdered state) (outside : index = id ∨ index < old) :
    ∀ row ∈ protectedRows state old id, row.capability.id ≠ index := by
  intro row member same
  have selected := (protectedRows_exact_selection state old id row).mp member
  rcases outside with equal | earlier
  · exact selected.2.1 (same.trans equal)
  · have absent := destinationDescendant_false_of_lt state ordered old index earlier
    simpa only [same, absent, Bool.false_eq_true] using selected.2.2.1

private theorem cleanup_original_leaf (state : ConstructionState) (old id : DestinationId)
    (row : PendingDestination) (present : state.destinations[old]? = some row)
    (different : old ≠ id) (indexed : DestinationCapabilitiesIndexed state)
    (allowed : (∃ count target, row.progress = .exiting count target) ∨
      row.progress = .abandoned ∨ row.progress = .cancelled) :
    ∃ current, (abandonRowsState (protectedRows state old id) state).destinations[old]? = some current ∧
      current.use = row.use ∧ current.backing = row.backing ∧ OwnershipLeafProgress current.progress := by
  have correct := indexed old row present
  have bounds := (protectedRows_indexed state old id indexed).1
  have unique := (protectedRows_indexed state old id indexed).2
  rcases allowed with ⟨count, target, exiting⟩ | abandoned | cancelled
  · have member : row ∈ protectedRows state old id := by
      apply (protectedRows_exact_selection state old id row).mpr
      refine ⟨Array.mem_toList_iff.mpr (Array.mem_iff_getElem?.mpr ⟨old, present⟩), ?_, ?_, ?_⟩
      · simpa only [correct] using different
      · simpa only [correct] using destinationDescendant_self state old (Array.getElem?_eq_some_iff.mp present).1
      · simp [activeRow, exiting]
    exact ⟨{ row with progress := .abandoned }, by
      simpa only [correct] using abandonRowsState_inside _ state bounds unique row member, rfl, rfl, by trivial⟩
  all_goals
    have outside : ∀ current ∈ protectedRows state old id, current.capability.id ≠ old := by
      intro current member same
      have found := protectedRows_current state old id indexed current member
      rw [same] at found
      have equal := Option.some.inj (present.symm.trans found)
      subst current
      have active := (protectedRows_exact_selection state old id row).mp member |>.2.2.2
      simp_all [activeRow]
    refine ⟨row, (abandonRowsState_outside _ state old outside).trans present, rfl, rfl, ?_⟩
    simp_all [OwnershipLeafProgress]

private theorem receiving_frame (id start payload : Nat) (state : ConstructionState) :
    ReservationMetadataFrame state (landReceivingStorage id start payload state).finalState ∧
      OwnershipForwardRowsFrame state (landReceivingStorage id start payload state).finalState ∧
      (landReceivingStorage id start payload state).finalState.destinations = state.destinations := by
  unfold landReceivingStorage
  cases present : state.storage[id]? with
  | none => exact ⟨.refl state, .refl state, rfl⟩
  | some storage =>
      simp only
      split
      · exact ⟨reservationMetadataFrame_storage state _ (by simp),
          ownershipForwardRowsFrame_same_rows state _ rfl, rfl⟩
      · exact ⟨.refl state, .refl state, rfl⟩

private def LandingParents (state : ConstructionState) (old id : Nat)
    (update : Option (DestinationId × PendingDestination)) : Prop :=
  ∀ parentId updated, update = some (parentId, updated) →
    ∃ parent count, state.destinations[parentId]? = some parent ∧
      parent.progress = .suspended count old ∧
      updated = { parent with progress := .suspended count id } ∧ parentId < old

private def landingUpdatedState (state : ConstructionState) (id : Nat) (landed : PendingDestination)
    (update : Option (DestinationId × PendingDestination)) : ConstructionState :=
  match update with
  | none => { state with destinations := state.destinations.set! id landed }
  | some (parentId, parent) =>
      { state with destinations := (state.destinations.set! id landed).set! parentId parent }

private theorem landing_updated_frame (state : ConstructionState) (id old count : Nat)
    (replacement superseded original : PendingDestination)
    (update : Option (DestinationId × PendingDestination))
    (present : state.destinations[id]? = some replacement)
    (originalPresent : state.destinations[old]? = some original)
    (replacementUse : replacement.use = .replacement old) (progress : replacement.progress = .built count)
    (originalLeaf : OwnershipLeafProgress original.progress)
    (sameUse : superseded.use = original.use) (sameBacking : replacement.backing = original.backing)
    (notReplacement : ∀ parent, superseded.use ≠ .replacement parent)
    (ordered : old < id) (parents : LandingParents state old id update) :
    let landed := { replacement with
      capability := { replacement.capability with start := superseded.capability.start }
      use := superseded.use
      progress := .built count
      writeEnd := replacement.writeEnd - (replacement.capability.start - superseded.capability.start)
      rollbackEnd := superseded.rollbackEnd }
    ReservationMetadataFrame state (landingUpdatedState state id landed update) ∧
      OwnershipForwardRowsFrame state (landingUpdatedState state id landed update) ∧
      (landingUpdatedState state id landed update).destinations[id]? = some landed := by
  dsimp only
  let landed := { replacement with
    capability := { replacement.capability with start := superseded.capability.start }
    use := superseded.use
    progress := DestinationProgress.built count
    writeEnd := replacement.writeEnd - (replacement.capability.start - superseded.capability.start)
    rollbackEnd := superseded.rollbackEnd }
  let changed := { state with destinations := state.destinations.set! id landed }
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have selected : changed.destinations[id]? = some landed := Array.getElem?_setIfInBounds_self_of_lt inside
  have firstMetadata : ReservationMetadataFrame state changed := by
    simpa only [List.append_nil] using reservationMetadataFrame_replace_mutable state id replacement landed
      state.storage [] present (Nat.le_refl _) (by simp [ReservationStableProgress, progress]) (by intros; rfl)
  have firstFrame : OwnershipForwardRowsFrame state changed :=
    ownershipForwardRowsFrame_adopt_replacement state id old count replacement landed original present originalPresent
      replacementUse progress originalLeaf (by trivial) notReplacement
  cases update with
  | none => exact ⟨firstMetadata, firstFrame, selected⟩
  | some pair =>
      obtain ⟨parentId, updated⟩ := pair
      obtain ⟨parent, parentCount, parentPresent, parentProgress, equal, earlier⟩ := parents parentId updated rfl
      subst updated
      have beforeSelected : parentId ≠ id := Nat.ne_of_lt (Nat.lt_trans earlier ordered)
      have parentAfter : changed.destinations[parentId]? = some parent := by
        simpa only [changed, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne (Ne.symm beforeSelected)] using parentPresent
      have oldAfter : changed.destinations[old]? = some original := by
        simpa only [changed, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne (Nat.ne_of_lt ordered).symm] using originalPresent
      have secondMetadata : ReservationMetadataFrame changed
          { changed with destinations := changed.destinations.set! parentId { parent with progress := .suspended parentCount id } } := by
        simpa only [List.append_nil] using reservationMetadataFrame_replace_mutable changed parentId parent _
          changed.storage [] parentAfter (Nat.le_refl _) (by simp [ReservationStableProgress, parentProgress]) (by intros; rfl)
      have secondFrame := ownershipForwardRowsFrame_land_parent changed parentId old id parentCount parent original landed
        parentAfter oldAfter selected parentProgress sameUse sameBacking
      exact ⟨firstMetadata.trans secondMetadata,
        OwnershipForwardRowsFrame.trans firstMetadata secondMetadata firstFrame secondFrame,
        by simpa only [landingUpdatedState, changed, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne beforeSelected] using selected⟩

private theorem relocate_frame (state : ConstructionState) (id count : Nat)
    (row : PendingDestination) (present : state.destinations[id]? = some row)
    (progress : row.progress = .built count) (relocate : Prop) [Decidable relocate] :
    ReservationMetadataFrame state { state with events := state.events ++
      (if relocate then [.relocate id .exitValue] else []) } ∧
      OwnershipForwardRowsFrame state { state with events := state.events ++
        (if relocate then [.relocate id .exitValue] else []) } := by
  constructor
  · apply reservationMetadataFrame_emit_mutable state id row _ present
    · simp [ReservationStableProgress, progress]
    · intro index different
      by_cases enabled : relocate <;> simp [enabled, destinationObservations, observeDestination, Ne.symm different]
  · exact ownershipForwardRowsFrame_same_rows state _ rfl

private theorem landingUpdates_result (state : ConstructionState) (id old count : Nat)
    (replacement superseded : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (present : state.destinations[id]? = some replacement) (parents : LandingParents state old id update) :
    let landed := { replacement with
      capability := { replacement.capability with start := superseded.capability.start }
      use := superseded.use
      progress := .built count
      writeEnd := replacement.writeEnd - (replacement.capability.start - superseded.capability.start)
      rollbackEnd := superseded.rollbackEnd }
    landingUpdates id count replacement superseded update state = .ok ()
      { landingUpdatedState state id landed update with events := state.events ++
        (if superseded.capability.start < replacement.capability.start then [.relocate id .exitValue] else []) } := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  cases update with
  | none =>
      by_cases relocate : superseded.capability.start < replacement.capability.start <;>
        simp [landingUpdates, landingUpdatedState, replaceDestination, emit,
          replaceDestination_result, emit_result, inside, relocate, bind, pure]
  | some pair =>
      obtain ⟨parentId, updated⟩ := pair
      obtain ⟨parent, parentCount, parentPresent, _, _, _⟩ := parents parentId updated rfl
      have parentInside := (Array.getElem?_eq_some_iff.mp parentPresent).1
      by_cases relocate : superseded.capability.start < replacement.capability.start <;>
        simp [landingUpdates, landingUpdatedState, replaceDestination, emit,
          replaceDestination_result, emit_result, inside, parentInside, relocate, bind, pure]

private theorem landing_remaining_frame (state : ConstructionState) (id old count : Nat)
    (replacement superseded original : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (present : state.destinations[id]? = some replacement) (originalPresent : state.destinations[old]? = some original)
    (replacementUse : replacement.use = .replacement old) (progress : replacement.progress = .built count)
    (originalLeaf : OwnershipLeafProgress original.progress)
    (sameUse : superseded.use = original.use) (sameBacking : replacement.backing = original.backing)
    (notReplacement : ∀ parent, superseded.use ≠ .replacement parent)
    (ordered : old < id) (parents : LandingParents state old id update) :
    ReservationMetadataFrame state (landingUpdates id count replacement superseded update state).finalState ∧
      OwnershipForwardRowsFrame state (landingUpdates id count replacement superseded update state).finalState := by
  have updated := landing_updated_frame state id old count replacement superseded original update present
    originalPresent replacementUse progress originalLeaf sameUse sameBacking notReplacement ordered parents
  let landed := { replacement with
    capability := { replacement.capability with start := superseded.capability.start }
    use := superseded.use
    progress := DestinationProgress.built count
    writeEnd := replacement.writeEnd - (replacement.capability.start - superseded.capability.start)
    rollbackEnd := superseded.rollbackEnd }
  have relocated := relocate_frame (landingUpdatedState state id landed update) id count landed updated.2.2 rfl
    (superseded.capability.start < replacement.capability.start)
  rw [landingUpdates_result state id old count replacement superseded update present parents]
  have combined := And.intro (updated.1.trans relocated.1)
    (OwnershipForwardRowsFrame.trans updated.1 relocated.1 updated.2.1 relocated.2)
  cases update <;> simpa only [ConstructionResult.finalState, landingUpdatedState, landed] using combined

private theorem completedFlow_ownership_frame (state : ConstructionState) (id old count : Nat)
    (replacement superseded : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (present : state.destinations[id]? = some replacement) (oldPresent : state.destinations[old]? = some superseded)
    (use : replacement.use = .replacement old) (progress : replacement.progress = .built count)
    (backing : replacement.backing = superseded.backing)
    (oldAllowed : (∃ count target, superseded.progress = .exiting count target) ∨
      superseded.progress = .abandoned ∨ superseded.progress = .cancelled)
    (notReplacement : ∀ parent, superseded.use ≠ .replacement parent)
    (ordered : old < id) (parents : LandingParents state old id update)
    (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (completedFlow id old count replacement superseded update state).finalState ∧
      OwnershipForwardRowsFrame state (completedFlow id old count replacement superseded update state).finalState := by
  simp only [completedFlow, lookupStorage, lookupStorage_result, bind]
  cases stored : state.storage[replacement.storage]? with
  | none => exact ⟨.refl state, .refl state⟩
  | some storage =>
      simp only [stored, pure, bind]
      by_cases backwards : replacement.capability.start < superseded.capability.start
      · simp only [backwards, ↓reduceIte, ConstructionM.fail, bind, ConstructionResult.finalState]
        exact ⟨.refl state, .refl state⟩
      · simp only [backwards, ↓reduceIte, ConstructionM.get, pure, bind]
        let rows := protectedRows state old id
        let cleaned := abandonRowsState rows state
        have current := protectedRows_current state old id valid.2.1
        have bounds := (protectedRows_indexed state old id valid.2.1).1
        have unique := (protectedRows_indexed state old id valid.2.1).2
        have cleanup := abandonRowsState_ownership_frame rows state current unique
        rw [protectedCleanup_exact rows state bounds]
        simp only [bind]
        have replacementAfter : cleaned.destinations[id]? = some replacement :=
          (abandonRowsState_outside rows state id
            (protectedRows_omit state old id id valid.2.2.2 (Or.inl rfl))).trans present
        obtain ⟨original, originalPresent, originalUse, originalBacking, originalLeaf⟩ :=
          cleanup_original_leaf state old id superseded oldPresent (Nat.ne_of_lt ordered) valid.2.1 oldAllowed
        have parentsAfter : LandingParents cleaned old id update := by
          intro parentId updated selected
          obtain ⟨parent, parentCount, parentPresent, parentProgress, equal, earlier⟩ := parents parentId updated selected
          refine ⟨parent, parentCount, ?_, parentProgress, equal, earlier⟩
          exact (abandonRowsState_outside rows state parentId
            (protectedRows_omit state old id parentId valid.2.2.2 (Or.inr earlier))).trans parentPresent
        have receiving := receiving_frame replacement.storage superseded.capability.start replacement.capability.start cleaned
        cases received : landReceivingStorage replacement.storage superseded.capability.start replacement.capability.start cleaned with
        | fault fault after =>
            simp only [received, ConstructionResult.finalState] at receiving
            simp only [received, bind, ConstructionResult.finalState]
            exact ⟨cleanup.1.trans receiving.1,
              OwnershipForwardRowsFrame.trans cleanup.1 receiving.1 cleanup.2 receiving.2.1⟩
        | ok value after =>
            simp only [received, ConstructionResult.finalState] at receiving
            simp only [received, bind]
            have rest := landing_remaining_frame after id old count replacement superseded original update
              (by simpa only [receiving.2.2] using replacementAfter)
              (by simpa only [receiving.2.2] using originalPresent)
              use progress originalLeaf originalUse.symm (backing.trans originalBacking.symm) notReplacement ordered
              (by simpa only [LandingParents, receiving.2.2] using parentsAfter)
            exact ⟨cleanup.1.trans (receiving.1.trans rest.1),
              OwnershipForwardRowsFrame.trans cleanup.1 (receiving.1.trans rest.1) cleanup.2
                (OwnershipForwardRowsFrame.trans receiving.1 rest.1 receiving.2.1 rest.2)⟩

private theorem completedStep_ownership_frame (state : ConstructionState) (id old count : Nat)
    (replacement superseded : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (present : state.destinations[id]? = some replacement) (oldPresent : state.destinations[old]? = some superseded)
    (use : replacement.use = .replacement old) (progress : replacement.progress = .built count)
    (backing : replacement.backing = superseded.backing)
    (oldAllowed : (∃ count target, superseded.progress = .exiting count target) ∨
      superseded.progress = .abandoned ∨ superseded.progress = .cancelled)
    (notReplacement : ∀ parent, superseded.use ≠ .replacement parent)
    (ordered : old < id) (parents : LandingParents state old id update)
    (valid : DestinationLifecycleInvariant state) :
    OwnershipForwardRowsFrame state (completedStep id old count replacement superseded update state).finalState := by
  rw [completedStep_flow]
  exact (completedFlow_ownership_frame state id old count replacement superseded update present oldPresent
    use progress backing oldAllowed notReplacement ordered parents valid).2

private abbrev landingLookupDestination (id : DestinationId) : ConstructionM PendingDestination := fun state =>
  (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left) (lookupDestination_result id state)

set_option maxHeartbeats 2000000 in
theorem landExitReplacement_ownership_frame (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state)
    (authority : SupportedReplacementAuthority state) :
    OwnershipForwardRowsFrame state (landExitReplacement id state).finalState := by
  simp only [landExitReplacement, landingLookupDestination, lookupDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some replacement =>
      simp only [present]
      cases use : replacement.use <;> try simp only [use] <;> try exact .refl state
      case replacement old =>
        cases progress : replacement.progress <;> try simp only [progress] <;> try exact .refl state
        case built count =>
          simp only [pure, bind, landingLookupDestination, lookupDestination_result]
          have orderedIds : old < id := by simpa only [use] using valid.2.2.2 id replacement present
          cases oldPresent : state.destinations[old]? with
          | none => exact .refl state
          | some superseded =>
              simp only [oldPresent, bind]
              obtain ⟨original, originalFound, backing, allowed⟩ :=
                active_replacement_original_exact state authority id old replacement present use
                  (by simp [activeProgress, progress])
              have equal := Option.some.inj (oldPresent.symm.trans originalFound)
              subst original
              have oldAllowed : (∃ count target, superseded.progress = .exiting count target) ∨
                  superseded.progress = .abandoned ∨ superseded.progress = .cancelled := by
                rcases allowed with ⟨prior, exiting⟩ | abandoned | cancelled
                · exact Or.inl ⟨prior, id, exiting⟩
                · exact Or.inr (Or.inl abandoned)
                · exact Or.inr (Or.inr cancelled)
              have finishNone (notReplacement : ∀ parent, superseded.use ≠ .replacement parent) := completedStep_ownership_frame state id old count replacement superseded none
                present oldPresent use progress backing oldAllowed notReplacement orderedIds
                (by intro parentId updated impossible; cases impossible) valid
              have finishChild : ∀ parentId parent parentCount,
                  superseded.use = .child parentId → state.destinations[parentId]? = some parent →
                  parent.progress = .suspended parentCount old →
                  OwnershipForwardRowsFrame state (completedStep id old count replacement superseded
                    (some (parentId, { parent with progress := .suspended parentCount id })) state).finalState := by
                intro parentId parent parentCount oldUse parentPresent parentProgress
                apply completedStep_ownership_frame state id old count replacement superseded _
                  present oldPresent use progress backing oldAllowed (by intro target; simp [oldUse]) orderedIds
                · intro index updated selected
                  cases selected
                  exact ⟨parent, parentCount, parentPresent, parentProgress, rfl,
                    by simpa only [oldUse] using valid.2.2.2 old superseded oldPresent⟩
                · exact valid
              have finishUse : OwnershipForwardRowsFrame state (((do
                  let parentUpdate ← match superseded.use with
                    | .receiver => pure none
                    | .child parentId => do
                        let parent ← landingLookupDestination parentId
                        match parent.progress with
                        | .suspended parentCount expected =>
                            if expected != old then ConstructionM.fail .ownership
                            pure (some (parentId, { parent with progress := .suspended parentCount id }))
                        | _ => ConstructionM.fail .protocol
                    | .replacement _ => ConstructionM.fail .protocol
                  completedStep id old count replacement superseded parentUpdate) : ConstructionM Unit) state).finalState := by
                cases oldUse : superseded.use with
                | receiver => exact finishNone (by intro target; simp [oldUse])
                | replacement prior => exact .refl state
                | child parentId =>
                    simp only [landingLookupDestination, lookupDestination_result, bind]
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
                  simp only [landingLookupDestination, lookupDestination_result, completedStep, bind, pure,
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

end Goose.Proofs.ConstructionExecutionOwnership
