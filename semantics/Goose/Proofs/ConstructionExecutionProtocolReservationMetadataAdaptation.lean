import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataWrites
import Goose.Proofs.ConstructionExecutionProtocolAdaptation

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
      destinations := state.destinations.set! id after} ∧
      ReservationMetadataFrame state { state with storage := storage, destinations := state.destinations.set! id after } := by
  constructor
  · exact destinationLifecycleInvariant_replace_silent state id before after storage present size
      capability backing use
      (by intro phase matched
          simpa only [DestinationTracePhase.matchesDestination, progress, backing, use] using matched) valid
  · exact (reservationMetadataFrame_storage state storage (Nat.le_of_eq size.symm)).trans
      (reservationMetadataFrame_replace { state with storage := storage } id before after present progress)

set_option maxHeartbeats 1000000 in
private theorem adaptConstructionDestination_pair (id : DestinationId)
    (producerType : Construct.Ty) (request : ConstructionRequest)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (adaptConstructionDestination id producerType request state).finalState ∧
      ReservationMetadataFrame state (adaptConstructionDestination id producerType request state).finalState := by
  simp only [adaptConstructionDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact ⟨valid, .refl state⟩
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact ⟨valid, .refl state⟩
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have storageInside := (valid.2.2.1 id destination present).1
          cases progress : destination.progress <;> try simp only [progress] <;> try exact ⟨valid, .refl state⟩
          case «open» count =>
            cases count with
            | succ count => exact ⟨valid, .refl state⟩
            | zero =>
                cases stored : state.storage[destination.storage]?
                all_goals repeat' first
                  | exact ⟨valid, .refl state⟩
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

private abbrev PreservesMetadata (action : ConstructionM α) : Prop :=
  ∀ state, ReservationMetadataFrame state (action state).finalState

private theorem metadata_pure (value : α) : PreservesMetadata (pure value) := fun state => .refl state
private theorem metadata_fail (kind : ConstructionFault) :
    PreservesMetadata (ConstructionM.fail (α := α) kind) := fun state => .refl state
private theorem metadata_fault_bind (kind : ConstructionFault) (next : α → ConstructionM β) :
    PreservesMetadata (ConstructionM.fail kind >>= next) := fun state => .refl state
private theorem metadata_get : PreservesMetadata ConstructionM.get := fun state => .refl state

private theorem metadata_bind (action : ConstructionM α) (next : α → ConstructionM β)
    (first : PreservesMetadata action) (remaining : ∀ value, PreservesMetadata (next value)) :
    PreservesMetadata (action >>= next) := reservationMetadataFrame_bind action next first remaining

private theorem metadata_if (condition : Prop) [Decidable condition] (yes no : ConstructionM α)
    (first : PreservesMetadata yes) (second : PreservesMetadata no) :
    PreservesMetadata (if condition then yes else no) := by
  by_cases selected : condition <;> simp only [selected, ↓reduceIte] <;> assumption

private theorem metadata_final_update (query : ConstructionM PendingDestination)
    (update : PendingDestination → ConstructionM Unit) (id : DestinationId)
    (queryResult : ∀ state, query state = match state.destinations[id]? with
      | some destination => .ok destination state
      | none => .fault .destination state)
    (safe : ∀ state destination, state.destinations[id]? = some destination →
      ReservationMetadataFrame state (update destination state).finalState) :
    PreservesMetadata (query >>= update) := by
  intro state
  simp only [bind, queryResult]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some destination => exact safe state destination present

private theorem metadata_progress_commit (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (storage : Array ReceivingStorage)
    (present : state.destinations[id]? = some before) (size : storage.size = state.storage.size)
    (progress : after.progress = before.progress) :
    ReservationMetadataFrame state { state with storage := storage, destinations := state.destinations.set! id after } :=
  (reservationMetadataFrame_storage state storage (Nat.le_of_eq size.symm)).trans
    (reservationMetadataFrame_replace { state with storage := storage } id before after present progress)

set_option maxHeartbeats 2000000 in
private theorem finishConstructionAdaptation_metadata (id : DestinationId) :
    PreservesMetadata (finishConstructionAdaptation id) := by
  unfold finishConstructionAdaptation
  repeat' first
    | with_reducible exact metadata_pure _
    | with_reducible exact metadata_fail _
    | with_reducible exact metadata_fault_bind _ _
    | with_reducible exact metadata_get
    | with_reducible exact removeConstructionHeader_metadata_frame _
    | solve
      | with_reducible apply metadata_final_update _ _ id
        · intro state
          exact lookupDestination_result id state
        · intro state current present
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          simp only [replaceDestination_result, inside, ↓reduceIte, ConstructionResult.finalState]
          exact metadata_progress_commit state id current _ state.storage present rfl rfl
    | solve
      | intro state
        simp only [lookupDestination_result, lookupStorage_result, writableDestination_result,
          replaceStorage_result]
        repeat' first
          | exact .refl state
          | solve
            | apply reservationMetadataFrame_storage state _
              simp [Array.set!_eq_setIfInBounds]
          | split
    | with_reducible apply metadata_bind
    | with_reducible apply metadata_if
    | dsimp only
    | split
    | intro value

set_option maxHeartbeats 2000000 in
private theorem normalizeProducerDestination_metadata (id : DestinationId) (producerType : Construct.Ty) :
    PreservesMetadata (normalizeProducerDestination id producerType) := by
  unfold normalizeProducerDestination
  repeat' first
    | with_reducible exact metadata_pure _
    | with_reducible exact metadata_fail _
    | with_reducible exact metadata_fault_bind _ _
    | with_reducible exact metadata_get
    | with_reducible exact removeConstructionHeader_metadata_frame _
    | solve
      | with_reducible apply metadata_final_update _ _ id
        · intro state
          exact lookupDestination_result id state
        · intro state current present
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          simp only [replaceDestination_result, inside, ↓reduceIte, ConstructionResult.finalState]
          exact metadata_progress_commit state id current _ state.storage present rfl rfl
    | solve
      | intro state
        simp only [lookupDestination_result, lookupStorage_result, writableDestination_result,
          replaceStorage_result]
        repeat' first
          | exact .refl state
          | solve
            | apply reservationMetadataFrame_storage state _
              simp [Array.set!_eq_setIfInBounds]
          | split
    | with_reducible apply metadata_bind
    | with_reducible apply metadata_if
    | dsimp only
    | split
    | intro value

theorem adaptConstructionDestination_reservation_frame (id : DestinationId)
    (producerType : Construct.Ty) (request : ConstructionRequest)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (adaptConstructionDestination id producerType request state).finalState :=
  (adaptConstructionDestination_pair id producerType request state valid).2

theorem finishConstructionAdaptation_reservation_frame (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (finishConstructionAdaptation id state).finalState :=
  finishConstructionAdaptation_metadata id state

theorem normalizeProducerDestination_reservation_frame (id : DestinationId) (producerType : Construct.Ty)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (normalizeProducerDestination id producerType state).finalState :=
  normalizeProducerDestination_metadata id producerType state

#print axioms adaptConstructionDestination_reservation_frame
#print axioms finishConstructionAdaptation_reservation_frame
#print axioms normalizeProducerDestination_reservation_frame

end Goose.Proofs.ConstructionExecutionProtocol
