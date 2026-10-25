import Goose.Construct.Destination

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

private abbrev destinationLookup (id : DestinationId) : ConstructionM PendingDestination := fun state =>
  (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left)
    (lookupDestination_result id state)

private abbrev storageLookup (id : StorageId) : ConstructionM ReceivingStorage := fun state =>
  (fun {left right : ConstructionResult ReceivingStorage} (_ : left = right) => left)
    (lookupStorage_result id state)

private abbrev destinationReplace (id : DestinationId) (destination : PendingDestination) : ConstructionM Unit := fun state =>
  (fun {left right : ConstructionResult Unit} (_ : left = right) => left)
    (replaceDestination_result id destination state)

private abbrev eventEmit (event : ConstructionEvent) : ConstructionM Unit := fun state =>
  (fun {left right : ConstructionResult Unit} (_ : left = right) => left) (emit_result event state)

private abbrev KeepsState (action : ConstructionM α) : Prop :=
  ∀ state, (action state).finalState = state

private theorem keepsState_bind (action : ConstructionM α) (next : α → ConstructionM β)
    (first : KeepsState action) (remaining : ∀ value, KeepsState (next value)) :
    KeepsState (action >>= next) := by
  intro state
  have same := first state
  cases result : action state with
  | ok value after =>
      simp only [result, ConstructionResult.finalState] at same
      simpa only [bind, result, same] using remaining value state
  | fault reason after => simpa only [bind, result, ConstructionResult.finalState] using same

private theorem keepsState_lookup (id : DestinationId) : KeepsState (destinationLookup id) := by
  intro state
  simp only [destinationLookup, lookupDestination_result]
  cases state.destinations[id]? <;> rfl

theorem exitLandingAnchor_finalState (fuel : Nat) (id : DestinationId) (storage : StorageId)
    (receiving : Option DestinationId) (state : ConstructionState) :
    (exitLandingAnchor fuel id storage receiving state).finalState = state := by
  have query : KeepsState (exitLandingAnchor fuel id storage receiving) := by
    induction fuel generalizing id storage receiving with
    | zero => exact fun _ => rfl
    | succ fuel ih =>
        simp only [exitLandingAnchor]
        repeat' first
          | exact fun _ => rfl
          | with_reducible exact keepsState_lookup _
          | with_reducible exact ih _ _ _
          | with_reducible apply keepsState_bind
          | split
          | (guard_target = ∀ _, KeepsState _; intro value)
  exact query state

private abbrev KeepsStdout (action : ConstructionM α) : Prop :=
  ∀ state, (action state).finalState.stdout = state.stdout

private theorem keepsStdout_bind (action : ConstructionM α) (next : α → ConstructionM β)
    (first : KeepsStdout action) (remaining : ∀ value, KeepsStdout (next value)) :
    KeepsStdout (action >>= next) := by
  intro state
  have same := first state
  cases result : action state with
  | ok value after =>
      simp only [result, ConstructionResult.finalState] at same
      simpa only [bind, result] using (remaining value after).trans same
  | fault reason after => simpa only [bind, result, ConstructionResult.finalState] using same

private theorem keepsStdout_lookup (id : DestinationId) : KeepsStdout (destinationLookup id) := by
  intro state
  rw [keepsState_lookup id state]

private theorem keepsStdout_storage (id : StorageId) : KeepsStdout (storageLookup id) := by
  intro state
  simp only [storageLookup, lookupStorage_result]
  cases state.storage[id]? <;> rfl

private theorem keepsStdout_replace (id : DestinationId) (destination : PendingDestination) :
    KeepsStdout (destinationReplace id destination) := by
  intro state
  simp only [destinationReplace, replaceDestination_result]
  split <;> rfl

private theorem keepsStdout_emit (event : ConstructionEvent) : KeepsStdout (eventEmit event) := by
  intro state
  simp only [eventEmit, emit_result]
  rfl

private theorem keepsStdout_landStorage (id : StorageId) (start payload : Nat) :
    KeepsStdout (landReceivingStorage id start payload) := by
  intro state
  unfold landReceivingStorage
  cases state.storage[id]? <;> simp only
  · rfl
  · split <;> rfl

private theorem keepsStdout_protected (action : List PendingDestination → ConstructionM Unit)
    (nilResult : ∀ state, action [] state = .ok () state)
    (consResult : ∀ destination rest state,
      action (destination :: rest) state =
        if destination.capability.id < state.destinations.size then
          action rest { state with
            destinations := state.destinations.set! destination.capability.id
              { destination with progress := .abandoned }
            events := state.events ++ [.abandon destination.capability.id] }
        else .fault .destination state)
    (rows : List PendingDestination) : KeepsStdout (action rows) := by
  induction rows with
  | nil => intro state; rw [nilResult]; rfl
  | cons destination rest ih =>
      intro state
      rw [consResult]
      split
      · exact ih _
      · rfl

private abbrev completedLanding (id old : DestinationId) (count : Nat)
    (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination)) : ConstructionM Unit :=
  (fun {left right : ConstructionM Unit} (_ : left = right) => left)
    (landCompletedReplacement_transition id old count replacement superseded parentUpdate)

private theorem keepsStdout_completed (id old : DestinationId) (count : Nat)
    (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination)) :
    KeepsStdout (completedLanding id old count replacement superseded parentUpdate) := by
  simp only [completedLanding, landCompletedReplacement_transition]
  repeat' first
    | exact fun _ => rfl
    | with_reducible exact keepsStdout_lookup _
    | with_reducible exact keepsStdout_storage _
    | with_reducible exact keepsStdout_replace _ _
    | with_reducible exact keepsStdout_emit _
    | with_reducible exact keepsStdout_landStorage _ _ _
    | solve
      | with_reducible apply keepsStdout_protected
        · exact protectedAbandonment_nil_transition
        · exact protectedAbandonment_cons_transition
    | with_reducible apply keepsStdout_bind
    | split
    | (guard_target = ∀ _, KeepsStdout _; intro value)

theorem commitExitReplacement_stdout (receiving : Option DestinationId) (id : DestinationId)
    (state : ConstructionState) :
    (commitExitReplacement receiving id state).finalState.stdout = state.stdout := by
  have preserved : KeepsStdout (commitExitReplacement receiving id) := by
    unfold commitExitReplacement
    repeat' first
      | exact fun _ => rfl
      | with_reducible exact keepsStdout_lookup _
      | with_reducible exact keepsStdout_completed _ _ _ _ _ _
      | solve
        | intro current
          rw [exitLandingAnchor_finalState]
      | with_reducible apply keepsStdout_bind
      | split
      | (guard_target = ∀ _, KeepsStdout _; intro value)
  exact preserved state

theorem landExitReplacementChain_stdout (id : DestinationId) (state : ConstructionState) :
    (landExitReplacementChain id state).finalState.stdout = state.stdout :=
  commitExitReplacement_stdout none id state

theorem landExitReplacementInto_stdout (receiving id : DestinationId) (state : ConstructionState) :
    (landExitReplacementInto receiving id state).finalState.stdout = state.stdout :=
  commitExitReplacement_stdout (some receiving) id state

end Goose.Proofs.ConstructionExecutionProtocol
