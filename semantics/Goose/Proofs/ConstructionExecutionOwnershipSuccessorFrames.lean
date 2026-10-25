import Goose.Proofs.ConstructionExecutionOwnershipCleanup
import Goose.Proofs.ConstructionExecutionOwnershipSuccessors
import Goose.Proofs.ConstructionExecutionOwnershipSuccessorLanding
import Lean

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

abbrev SuccessorFrame (before after : ConstructionState) : Prop :=
  after.destinationSuccessors = before.destinationSuccessors ∧
    after.destinations.size = before.destinations.size

abbrev FramesSuccessors (action : ConstructionM α) : Prop :=
  ∀ state, SuccessorFrame state (action state).finalState

theorem successorFrame_refl (state : ConstructionState) : SuccessorFrame state state := ⟨rfl, rfl⟩

theorem successorFrame_trans (before middle after : ConstructionState)
    (first : SuccessorFrame before middle) (second : SuccessorFrame middle after) : SuccessorFrame before after :=
  ⟨second.1.trans first.1, second.2.trans first.2⟩

theorem framesSuccessors_pure (value : α) : FramesSuccessors (pure value : ConstructionM α) :=
  fun _ => ⟨rfl, rfl⟩

theorem framesSuccessors_fail (reason : ConstructionFault) : FramesSuccessors (ConstructionM.fail reason : ConstructionM α) :=
  fun _ => ⟨rfl, rfl⟩

theorem framesSuccessors_bind (action : ConstructionM α) (next : α → ConstructionM β)
    (first : FramesSuccessors action) (remaining : ∀ value, FramesSuccessors (next value)) :
    FramesSuccessors (action >>= next) := by
  intro state
  cases result : action state with
  | fault reason after => simpa only [bind, result, ConstructionResult.finalState] using first state
  | ok value after =>
      have before := first state
      simp only [result, ConstructionResult.finalState] at before
      simpa only [bind, result] using successorFrame_trans state after _ before (remaining value after)

theorem framesSuccessors_get : FramesSuccessors ConstructionM.get := fun _ => ⟨rfl, rfl⟩

theorem protectedCleanup_successorFrame (rows : List PendingDestination) : FramesSuccessors (protectedCleanup rows) := by
  intro state
  induction rows generalizing state with
  | nil => simp only [protectedCleanup_nil, ConstructionResult.finalState]; exact ⟨rfl, rfl⟩
  | cons row rest ih =>
      rw [protectedCleanup_cons]
      split
      · simpa only [SuccessorFrame, Array.size_set!] using ih { state with
          destinations := state.destinations.set! row.capability.id { row with progress := .abandoned }
          events := state.events ++ [.abandon row.capability.id] }
      · exact ⟨rfl, rfl⟩

abbrev destinationLookup (id : DestinationId) : ConstructionM PendingDestination := fun state =>
  (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left)
    (lookupDestination_result id state)

theorem destinationLookup_successorFrame (id : DestinationId) : FramesSuccessors (destinationLookup id) := by
  intro state
  simp only [destinationLookup, lookupDestination_result]
  split <;> exact ⟨rfl, rfl⟩

abbrev storageLookup (id : StorageId) : ConstructionM ReceivingStorage := fun state =>
  (fun {left right : ConstructionResult ReceivingStorage} (_ : left = right) => left)
    (lookupStorage_result id state)

abbrev destinationReplace (id : DestinationId) (row : PendingDestination) : ConstructionM Unit := fun state =>
  (fun {left right : ConstructionResult Unit} (_ : left = right) => left)
    (replaceDestination_result id row state)

abbrev eventEmit (event : ConstructionEvent) : ConstructionM Unit := fun state =>
  (fun {left right : ConstructionResult Unit} (_ : left = right) => left) (emit_result event state)

theorem storageLookup_successorFrame (id : StorageId) : FramesSuccessors (storageLookup id) := by
  intro state
  simp only [storageLookup, lookupStorage_result]
  split <;> exact ⟨rfl, rfl⟩

theorem destinationReplace_successorFrame (id : DestinationId) (row : PendingDestination) :
    FramesSuccessors (destinationReplace id row) := by
  intro state
  simp only [destinationReplace, replaceDestination_result]
  split <;> simp [SuccessorFrame, ConstructionResult.finalState]

theorem eventEmit_successorFrame (event : ConstructionEvent) : FramesSuccessors (eventEmit event) :=
  fun _ => ⟨rfl, rfl⟩

theorem landReceivingStorage_successorFrame (id : StorageId) (receivingStart payloadStart : Nat) :
    FramesSuccessors (landReceivingStorage id receivingStart payloadStart) := by
  intro state
  simp only [landReceivingStorage]
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

abbrev storageReplace (id : StorageId) (storage : ReceivingStorage) : ConstructionM Unit := fun state =>
  (fun {left right : ConstructionResult Unit} (_ : left = right) => left)
    (replaceStorage_result id storage state)

theorem storageReplace_successorFrame (id : StorageId) (storage : ReceivingStorage) :
    FramesSuccessors (storageReplace id storage) := by
  intro state
  simp only [storageReplace, replaceStorage_result]
  split <;> exact ⟨rfl, rfl⟩

theorem framesSuccessors_preserves (action : ConstructionM α) (frame : FramesSuccessors action)
    (state : ConstructionState) (valid : DestinationSuccessorsValid state) :
    DestinationSuccessorsValid (action state).finalState := by
  have unchanged := frame state
  exact destinationSuccessorsValid_extension state _ valid unchanged.1 (Nat.le_of_eq unchanged.2.symm)

open Lean Elab Term Meta in
elab "protected_abandonment_head" : term => do
  let declaration ← getConstInfo ``Goose.Construct.protectedAbandonment_nil_transition
  forallTelescope declaration.type fun _ body => do
    let arguments := body.getAppArgs
    unless body.getAppFn.isConstOf ``Eq && arguments.size == 3 do
      throwError "expected a protected abandonment result equation"
    return arguments[1]!.getAppFn

private abbrev protectedAbandonmentAction : List PendingDestination → ConstructionM Unit :=
  protected_abandonment_head

private theorem protectedAbandonmentAction_eq (rows : List PendingDestination) :
    protectedAbandonmentAction rows = protectedCleanup rows := by
  funext state
  cases rows <;> rfl

abbrev completedLandingAction (replacementId supersededId : DestinationId) (count : Nat)
    (replacement superseded : PendingDestination) (parentUpdate : Option (DestinationId × PendingDestination)) :
    ConstructionM Unit :=
  (fun {left right : ConstructionM Unit} (_ : left = right) => left)
    (landCompletedReplacement_transition replacementId supersededId count replacement superseded parentUpdate)

theorem completedLandingAction_successorFrame (replacementId supersededId : DestinationId) (count : Nat)
    (replacement superseded : PendingDestination) (parentUpdate : Option (DestinationId × PendingDestination)) :
    FramesSuccessors (completedLandingAction replacementId supersededId count replacement superseded parentUpdate) := by
  simp only [completedLandingAction, landCompletedReplacement_transition]
  apply framesSuccessors_bind
  · exact storageLookup_successorFrame _
  · intro storage
    split
    · exact framesSuccessors_fail _
    · apply framesSuccessors_bind
      · exact framesSuccessors_get
      · intro state
        apply framesSuccessors_bind
        · change FramesSuccessors (protectedAbandonmentAction _)
          rw [protectedAbandonmentAction_eq]
          exact protectedCleanup_successorFrame _
        · intro discarded
          apply framesSuccessors_bind
          · exact landReceivingStorage_successorFrame _ _ _
          · intro moved
            apply framesSuccessors_bind
            · exact destinationReplace_successorFrame _ _
            · intro selected
              cases parentUpdate with
              | none =>
                  simp only
                  split
                  · exact eventEmit_successorFrame _
                  · exact framesSuccessors_pure _
              | some update =>
                  rcases update with ⟨parentId, parent⟩
                  simp only
                  apply framesSuccessors_bind
                  · exact destinationReplace_successorFrame _ _
                  · intro updated
                    split
                    · exact eventEmit_successorFrame _
                    · exact framesSuccessors_pure _

theorem landExitReplacement_successorFrame (replacementId : DestinationId) :
    FramesSuccessors (landExitReplacement replacementId) := by
  unfold landExitReplacement
  apply framesSuccessors_bind
  · exact destinationLookup_successorFrame _
  · intro replacement
    cases use : replacement.use <;> cases progress : replacement.progress
    all_goals simp only [use, progress, bind, pure, ConstructionM.fail]
    all_goals try exact framesSuccessors_fail _
    rename_i supersededId count
    apply framesSuccessors_bind
    · exact destinationLookup_successorFrame _
    · intro superseded
      have finish : FramesSuccessors (do
          let parentUpdate ← match superseded.use with
            | .receiver => pure none
            | .child parentId => do
                let parent ← destinationLookup parentId
                match parent.progress with
                | .suspended parentCount expected =>
                    if expected != supersededId then ConstructionM.fail .ownership
                    pure (some (parentId, { parent with progress := .suspended parentCount replacementId }))
                | _ => ConstructionM.fail .protocol
            | .replacement _ => ConstructionM.fail .protocol
          completedLandingAction replacementId supersededId count replacement superseded parentUpdate) := by
        cases superseded.use with
        | receiver => exact completedLandingAction_successorFrame _ _ _ _ _ _
        | replacement _ => exact framesSuccessors_fail _
        | child parentId =>
            apply framesSuccessors_bind
            · exact destinationLookup_successorFrame _
            · intro parent
              cases parentProgress : parent.progress
              all_goals simp only [parentProgress, bind, pure, ConstructionM.fail]
              all_goals try exact framesSuccessors_fail _
              split
              · exact framesSuccessors_fail _
              · exact completedLandingAction_successorFrame _ _ _ _ _ _
      cases oldProgress : superseded.progress
      all_goals simp only [oldProgress]
      all_goals try exact framesSuccessors_fail _
      all_goals
        split
        · exact framesSuccessors_fail _
        · exact finish

end Goose.Proofs.ConstructionExecutionOwnership
