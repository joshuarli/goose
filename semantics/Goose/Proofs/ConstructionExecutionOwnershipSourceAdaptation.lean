import Goose.Proofs.ConstructionExecutionOwnershipSourceHeaders
import Goose.Proofs.ConstructionExecutionOwnershipSourceTable
import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataWrites
import Goose.Proofs.ConstructionExecutionProtocolAdaptation

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

private def AdaptationReady (state : ConstructionState) (id : DestinationId) : Prop :=
  ∀ row, state.destinations[id]? = some row → OwnershipLeafProgress row.progress

private def AdaptationAction (id : DestinationId) (action : ConstructionM α) : Prop :=
  ∀ state, AdaptationReady state id →
    ReservationMetadataFrame state (action state).finalState ∧
      OwnershipSourceExtension state (action state).finalState ∧ AdaptationReady (action state).finalState id

private theorem adaptationReady_replace (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (progress : after.progress = before.progress) (ready : AdaptationReady state id) :
    AdaptationReady { state with destinations := state.destinations.set! id after } id := by
  intro row found
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have equal : after = row := by
    simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside,
      Option.some.injEq] using found
  subst row
  simpa only [progress] using ready before present

private theorem adaptation_commit (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (storage : Array ReceivingStorage)
    (present : state.destinations[id]? = some before) (size : storage.size = state.storage.size)
    (sameUse : after.use = before.use) (sameBacking : after.backing = before.backing)
    (progress : after.progress = before.progress) (ready : AdaptationReady state id) :
    ReservationMetadataFrame state { state with storage := storage, destinations := state.destinations.set! id after } ∧
      OwnershipSourceExtension state { state with storage := storage, destinations := state.destinations.set! id after } ∧
      AdaptationReady { state with storage := storage, destinations := state.destinations.set! id after } id := by
  refine ⟨(reservationMetadataFrame_storage state storage (Nat.le_of_eq size.symm)).trans
    (reservationMetadataFrame_replace { state with storage := storage } id before after present progress), ?_, ?_⟩
  · refine ownershipSourceExtension_replace state id before after present sameUse ?_
    cases use : before.use <;> simp [OwnershipLinkBacking, use, sameBacking]
  · exact adaptationReady_replace state id before after present progress ready

private theorem adaptation_pure (id : DestinationId) (value : α) : AdaptationAction id (pure value) :=
  fun state ready => ⟨.refl state, .refl state, ready⟩

private theorem adaptation_fail (id : DestinationId) (fault : ConstructionFault) :
    AdaptationAction id (ConstructionM.fail (α := α) fault) := fun state ready => ⟨.refl state, .refl state, ready⟩

private theorem adaptation_fault_bind (id : DestinationId) (fault : ConstructionFault) (next : α → ConstructionM β) :
    AdaptationAction id (ConstructionM.fail fault >>= next) := fun state ready => ⟨.refl state, .refl state, ready⟩

private theorem adaptation_get (id : DestinationId) : AdaptationAction id ConstructionM.get :=
  fun state ready => ⟨.refl state, .refl state, ready⟩

private theorem adaptation_storage (state : ConstructionState) (id : DestinationId)
    (storage : Array ReceivingStorage) (size : state.storage.size ≤ storage.size) (ready : AdaptationReady state id) :
    ReservationMetadataFrame state { state with storage := storage } ∧
      OwnershipSourceExtension state { state with storage := storage } ∧ AdaptationReady { state with storage := storage } id :=
  ⟨reservationMetadataFrame_storage state storage size, ownershipSourceExtension_sameRows state _ rfl, ready⟩

private theorem adaptation_bind (id : DestinationId) (action : ConstructionM α) (next : α → ConstructionM β)
    (first : AdaptationAction id action) (remaining : ∀ value, AdaptationAction id (next value)) :
    AdaptationAction id (action >>= next) := by
  intro state ready
  have initial := first state ready
  cases result : action state with
  | fault fault final => simpa only [result, bind, ConstructionResult.finalState] using initial
  | ok value middle =>
      simp only [result, ConstructionResult.finalState] at initial
      have rest := remaining value middle initial.2.2
      simpa only [result, bind] using And.intro (initial.1.trans rest.1)
        (And.intro (ownershipSourceExtension_trans _ _ _ initial.2.1 rest.2.1) rest.2.2)

private theorem adaptation_if (id : DestinationId) (condition : Prop) [Decidable condition]
    (yes no : ConstructionM α) (first : AdaptationAction id yes) (second : AdaptationAction id no) :
    AdaptationAction id (if condition then yes else no) := by
  by_cases selected : condition <;> simp only [selected, ↓reduceIte] <;> assumption

private theorem adaptation_final_update (query : ConstructionM PendingDestination)
    (update : PendingDestination → ConstructionM Unit) (id : DestinationId)
    (queryResult : ∀ state, query state = match state.destinations[id]? with
      | some destination => .ok destination state
      | none => .fault .destination state)
    (safe : ∀ state destination, state.destinations[id]? = some destination →
      AdaptationReady state id → ReservationMetadataFrame state (update destination state).finalState ∧
        OwnershipSourceExtension state (update destination state).finalState ∧
        AdaptationReady (update destination state).finalState id) :
    AdaptationAction id (query >>= update) := by
  intro state ready
  simp only [bind, queryResult]
  cases present : state.destinations[id]? with
  | none => exact ⟨.refl state, .refl state, ready⟩
  | some destination => exact safe state destination present ready

local syntax "adaptation_split_if" : tactic
elab_rules : tactic
  | `(tactic| adaptation_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no ownership adaptation condition to split"
      return [yes.mvarId, no.mvarId]

private theorem removeConstructionHeader_ready (id : DestinationId)
    (state : ConstructionState) (ready : AdaptationReady state id) :
    AdaptationReady (removeConstructionHeader id state).finalState id := by
  simp only [removeConstructionHeader, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact ready
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact ready
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          cases progress : destination.progress <;> (try simp only [progress]) <;> try exact ready
          case built count =>
            have removed : ∀ storage : ReceivingStorage,
                AdaptationReady { state with
                  storage := state.storage.set! destination.storage storage
                  destinations := state.destinations.set! id { destination with layout := .elements, writeEnd := destination.writeEnd - 4 },
                  events := state.events ++ [.relocate id .headerRemoval] } id := by
              intro storage
              exact adaptationReady_replace state id destination _ present rfl ready
            simp only [progress] at removed
            cases stored : state.storage[destination.storage]? with
            | none =>
                repeat' first
                  | simp only [lookupStorage_result, stored, bind, ConstructionM.fail,
                      ConstructionResult.finalState]
                  | adaptation_split_if
                  | exact ready
            | some receiving =>
              have bound := (Array.getElem?_eq_some_iff.mp stored).choose
              repeat' first
                | simp only [lookupStorage_result, stored, replaceStorage_result,
                    replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                    ConstructionM.fail, emit_result, ConstructionResult.finalState]
                | adaptation_split_if
                | exact ready
                | exact removed _

private theorem adaptation_removeHeader (id : DestinationId) : AdaptationAction id (removeConstructionHeader id) := by
  intro state ready
  exact ⟨removeConstructionHeader_metadata_frame id state,
    removeConstructionHeader_ownership_source id state,
    removeConstructionHeader_ready id state ready⟩

set_option maxHeartbeats 2000000 in
private theorem finishConstructionAdaptation_ready (id : DestinationId) :
    AdaptationAction id (finishConstructionAdaptation id) := by
  unfold finishConstructionAdaptation
  repeat' first
    | with_reducible exact adaptation_pure id _
    | with_reducible exact adaptation_fail id _
    | with_reducible exact adaptation_fault_bind id _ _
    | with_reducible exact adaptation_get id
    | with_reducible exact adaptation_removeHeader _
    | solve
      | with_reducible apply adaptation_final_update _ _ id
        · intro state
          exact lookupDestination_result id state
        · intro state current present ready
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          simp only [replaceDestination_result, inside, ↓reduceIte, ConstructionResult.finalState]
          exact adaptation_commit state id current _ state.storage present rfl rfl rfl rfl ready
    | solve
      | intro state ready
        simp only [lookupDestination_result, lookupStorage_result, writableDestination_result,
          replaceStorage_result]
        repeat' first
          | exact ⟨.refl state, .refl state, ready⟩
          | solve
            | apply adaptation_storage state id _ _ ready
              simp [Array.set!_eq_setIfInBounds]
          | split
    | with_reducible apply adaptation_bind id
    | with_reducible apply adaptation_if id
    | dsimp only
    | split
    | intro value

set_option maxHeartbeats 2000000 in
private theorem normalizeProducerDestination_ready (id : DestinationId) (producerType : Construct.Ty) :
    AdaptationAction id (normalizeProducerDestination id producerType) := by
  unfold normalizeProducerDestination
  repeat' first
    | with_reducible exact adaptation_pure id _
    | with_reducible exact adaptation_fail id _
    | with_reducible exact adaptation_fault_bind id _ _
    | with_reducible exact adaptation_get id
    | with_reducible exact adaptation_removeHeader _
    | solve
      | with_reducible apply adaptation_final_update _ _ id
        · intro state
          exact lookupDestination_result id state
        · intro state current present ready
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          simp only [replaceDestination_result, inside, ↓reduceIte, ConstructionResult.finalState]
          exact adaptation_commit state id current _ state.storage present rfl rfl rfl rfl ready
    | solve
      | intro state ready
        simp only [lookupDestination_result, lookupStorage_result, writableDestination_result,
          replaceStorage_result]
        repeat' first
          | exact ⟨.refl state, .refl state, ready⟩
          | solve
            | apply adaptation_storage state id _ _ ready
              simp [Array.set!_eq_setIfInBounds]
          | split
    | with_reducible apply adaptation_bind id
    | with_reducible apply adaptation_if id
    | dsimp only
    | split
    | intro value

private theorem adaptationReady_of_leaf (state : ConstructionState) (id : DestinationId)
    (row : PendingDestination) (present : state.destinations[id]? = some row)
    (leaf : OwnershipLeafProgress row.progress) : AdaptationReady state id := by
  intro current found
  have equal := Option.some.inj (present.symm.trans found)
  subst current
  exact leaf

theorem finishConstructionAdaptation_ownership_source (id : DestinationId)
    (state : ConstructionState) : OwnershipSourceExtension state (finishConstructionAdaptation id state).finalState := by
  by_cases ready : AdaptationReady state id
  · exact (finishConstructionAdaptation_ready id state ready).2.1
  · cases present : state.destinations[id]? with
    | none =>
        apply False.elim
        apply ready
        intro current found
        simp only [present] at found
        contradiction
    | some row =>
        by_cases leaf : OwnershipLeafProgress row.progress
        · exact False.elim (ready (adaptationReady_of_leaf state id row present leaf))
        · cases progress : row.progress <;> simp [progress, OwnershipLeafProgress] at leaf
          all_goals
            cases allowed : destinationCanWrite state id
            all_goals cases adaptation : row.adaptation <;>
              simp only [finishConstructionAdaptation, lookupDestination_result, writableDestination_result, present, allowed, adaptation, progress,
                bind, pure, ConstructionM.fail, ConstructionResult.finalState]
            all_goals exact .refl state

theorem normalizeProducerDestination_ownership_source (id : DestinationId) (producerType : Construct.Ty)
    (state : ConstructionState) : OwnershipSourceExtension state (normalizeProducerDestination id producerType state).finalState := by
  by_cases ready : AdaptationReady state id
  · exact (normalizeProducerDestination_ready id producerType state ready).2.1
  · cases present : state.destinations[id]? with
    | none =>
        apply False.elim
        apply ready
        intro current found
        simp only [present] at found
        contradiction
    | some row =>
        by_cases leaf : OwnershipLeafProgress row.progress
        · exact False.elim (ready (adaptationReady_of_leaf state id row present leaf))
        · cases progress : row.progress <;> simp [progress, OwnershipLeafProgress] at leaf
          all_goals
            cases allowed : destinationCanWrite state id
            all_goals cases adaptation : row.adaptation <;>
              simp only [normalizeProducerDestination, lookupDestination_result, writableDestination_result, present, allowed, adaptation, progress,
                bind, pure, ConstructionM.fail, ConstructionResult.finalState]
            all_goals exact .refl state

set_option maxHeartbeats 1000000 in
theorem adaptConstructionDestination_ownership_source (id : DestinationId)
    (producerType : Construct.Ty) (request : ConstructionRequest)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    OwnershipSourceExtension state (adaptConstructionDestination id producerType request state).finalState := by
  simp only [adaptConstructionDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have storageInside := (valid.2.2.1 id destination present).1
          cases progress : destination.progress <;> try simp only [progress] <;> try exact .refl state
          case «open» count =>
            cases count with
            | succ count => exact .refl state
            | zero =>
                cases stored : state.storage[destination.storage]?
                all_goals repeat' first
                  | exact .refl state
                  | solve
                    | refine ownershipSourceExtension_replace state id destination _ present ?_ ?_
                      · rfl
                      · cases use : destination.use <;> simp [OwnershipLinkBacking, use]
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      lookupStorage_result, replaceDestination_result, replaceStorage_result,
                      inside, storageInside, stored, ↓reduceIte, bind, pure, ConstructionResult.finalState]
                  | adaptation_split_if
                  | split

end Goose.Proofs.ConstructionExecutionOwnership
