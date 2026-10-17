import Goose.Proofs.ConstructionExecutionProtocolWrites

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

local syntax "adaptation_split_if" : tactic
elab_rules : tactic
  | `(tactic| adaptation_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no adaptation condition to split"
      return [yes.mvarId, no.mvarId]

private theorem adapt_commit_lifecycle (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (storage : Array ReceivingStorage)
    (present : state.destinations[id]? = some before)
    (size : storage.size = state.storage.size)
    (capability : after.capability.id = before.capability.id)
    (backing : after.backing = before.backing) (use : after.use = before.use)
    (progress : after.progress = before.progress)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with
      storage := storage
      destinations := state.destinations.set! id after} := by
  exact destinationLifecycleInvariant_replace_silent state id before after storage present size
    capability backing use
    (by intro phase matched
        simpa only [DestinationTracePhase.matchesDestination, progress, backing, use] using matched) valid

private abbrev PreservesLifecycle (action : ConstructionM α) : Prop :=
  ∀ state, DestinationLifecycleInvariant state → DestinationLifecycleInvariant (action state).finalState

private theorem lifecycle_pure (value : α) : PreservesLifecycle (pure value) := fun _ valid => valid
private theorem lifecycle_fail (kind : ConstructionFault) :
    PreservesLifecycle (ConstructionM.fail (α := α) kind) := fun _ valid => valid
private theorem lifecycle_fault_bind (kind : ConstructionFault) (next : α → ConstructionM β) :
    PreservesLifecycle (ConstructionM.fail kind >>= next) := fun _ valid => valid
private theorem lifecycle_get : PreservesLifecycle ConstructionM.get := fun _ valid => valid

private theorem lifecycle_bind (action : ConstructionM α) (next : α → ConstructionM β)
    (first : PreservesLifecycle action) (remaining : ∀ value, PreservesLifecycle (next value)) :
    PreservesLifecycle (action >>= next) := by
  intro state valid
  have preserved := first state valid
  cases result : action state with
  | ok value after =>
      simpa only [bind, result] using remaining value after
        (by simpa only [result, ConstructionResult.finalState] using preserved)
  | fault kind after => simpa only [bind, result, ConstructionResult.finalState] using preserved

private theorem lifecycle_if (condition : Prop) [Decidable condition] (yes no : ConstructionM α)
    (first : PreservesLifecycle yes) (second : PreservesLifecycle no) :
    PreservesLifecycle (if condition then yes else no) := by
  by_cases selected : condition <;> simp only [selected, ↓reduceIte] <;> assumption

private theorem lifecycle_final_update (query : ConstructionM PendingDestination)
    (update : PendingDestination → ConstructionM Unit) (id : DestinationId)
    (queryResult : ∀ state, query state = match state.destinations[id]? with
      | some destination => .ok destination state
      | none => .fault .destination state)
    (safe : ∀ state destination, state.destinations[id]? = some destination →
      DestinationLifecycleInvariant state → DestinationLifecycleInvariant (update destination state).finalState) :
    PreservesLifecycle (query >>= update) := by
  intro state valid
  simp only [bind, queryResult]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some destination => exact safe state destination present valid

set_option maxHeartbeats 1000000 in
theorem adaptConstructionDestination_destination_lifecycle_invariant (id : DestinationId)
    (producerType : Construct.Ty) (request : ConstructionRequest)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (adaptConstructionDestination id producerType request state).finalState := by
  simp only [adaptConstructionDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact valid
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have storageInside := (valid.2.2.1 id destination present).1
          cases progress : destination.progress <;> try simp only [progress] <;> try exact valid
          case «open» count =>
            cases count with
            | succ count => exact valid
            | zero =>
                cases stored : state.storage[destination.storage]?
                all_goals repeat' first
                  | exact valid
                  | solve
                    | apply adapt_commit_lifecycle state id destination _ _ present
                      · simp [Array.set!_eq_setIfInBounds]
                      · rfl
                      · rfl
                      · rfl
                      · simp only [progress]
                      · exact valid
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      lookupStorage_result, replaceDestination_result, replaceStorage_result,
                      inside, storageInside, stored, ↓reduceIte, bind, pure, ConstructionResult.finalState]
                  | adaptation_split_if
                  | split

set_option maxHeartbeats 2000000 in
theorem finishConstructionAdaptation_destination_lifecycle_invariant (id : DestinationId) :
    PreservesLifecycle (finishConstructionAdaptation id) := by
  unfold finishConstructionAdaptation
  repeat' first
    | with_reducible exact lifecycle_pure _
    | with_reducible exact lifecycle_fail _
    | with_reducible exact lifecycle_fault_bind _ _
    | with_reducible exact lifecycle_get
    | with_reducible exact removeConstructionHeader_destination_lifecycle_invariant _
    | solve
      | with_reducible apply lifecycle_final_update _ _ id
        · intro state
          exact lookupDestination_result id state
        · intro state current present valid
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          simp only [replaceDestination_result, inside, ↓reduceIte, ConstructionResult.finalState]
          exact adapt_commit_lifecycle state id current _ state.storage present rfl rfl rfl rfl rfl valid
    | solve
      | intro state valid
        simp only [lookupDestination_result, lookupStorage_result, writableDestination_result,
          replaceStorage_result]
        repeat' first
          | exact valid
          | solve
            | apply destinationLifecycleInvariant_storage_frame state _ _ valid
              simp [Array.set!_eq_setIfInBounds]
          | split
    | with_reducible apply lifecycle_bind
    | with_reducible apply lifecycle_if
    | dsimp only
    | split
    | intro value

set_option maxHeartbeats 2000000 in
theorem normalizeProducerDestination_destination_lifecycle_invariant (id : DestinationId) (producerType : Construct.Ty) :
    PreservesLifecycle (normalizeProducerDestination id producerType) := by
  unfold normalizeProducerDestination
  repeat' first
    | with_reducible exact lifecycle_pure _
    | with_reducible exact lifecycle_fail _
    | with_reducible exact lifecycle_fault_bind _ _
    | with_reducible exact lifecycle_get
    | with_reducible exact removeConstructionHeader_destination_lifecycle_invariant _
    | solve
      | with_reducible apply lifecycle_final_update _ _ id
        · intro state
          exact lookupDestination_result id state
        · intro state current present valid
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          simp only [replaceDestination_result, inside, ↓reduceIte, ConstructionResult.finalState]
          exact adapt_commit_lifecycle state id current _ state.storage present rfl rfl rfl rfl rfl valid
    | solve
      | intro state valid
        simp only [lookupDestination_result, lookupStorage_result, writableDestination_result,
          replaceStorage_result]
        repeat' first
          | exact valid
          | solve
            | apply destinationLifecycleInvariant_storage_frame state _ _ valid
              simp [Array.set!_eq_setIfInBounds]
          | split
    | with_reducible apply lifecycle_bind
    | with_reducible apply lifecycle_if
    | dsimp only
    | split
    | intro value

end Goose.Proofs.ConstructionExecutionProtocol
