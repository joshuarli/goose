import Goose.Proofs.ConstructionExecutionProtocolReservationRearm
import Goose.Construct.Destination
import Goose.Proofs.ConstructionExecutionProtocolQueries
import Goose.Proofs.ConstructionExecutionProtocolReservationKernel
import Goose.Proofs.ConstructionExecutionProtocolReservationFrontier
import Lean.Elab.Tactic.Split
import Goose.Proofs.ConstructionExecutionProtocolReservationCombinators

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionEventPrefixProtocol
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionProtocol

abbrev PrefixInvariant (before : List ConstructionEvent) (state : ConstructionState) : Prop := before <+: state.events

abbrev PreservesPrefixInvariant (before : List ConstructionEvent) (action : ConstructionM α) : Prop :=
  ∀ state, PrefixInvariant before state → PrefixInvariant before (action state).finalState

variable {before : List ConstructionEvent}

private theorem prefix_of_native (action : ConstructionM α) (safe : PreservesEventPrefix action) :
    PreservesPrefixInvariant before action := fun state valid => valid.trans (safe state)

private theorem rearmExitReservation_events_prefix (borrowed : BorrowedWaitingExitReservation) :
    PreservesPrefixInvariant before (rearmExitReservation borrowed) := by
  intro state valid
  have frame := Goose.Proofs.ConstructionExecutionOwnership.rearmExitReservation_preserves_construction state borrowed
  change before <+: (rearmExitReservation borrowed state).finalState.events
  rw [frame.2.2.1]
  exact valid

private theorem prefix_landReceivingStorage (storage start count : Nat) :
    PreservesPrefixInvariant before (landReceivingStorage storage start count) := by
  intro state valid
  cases present : state.storage[storage]? with
  | none => simpa [landReceivingStorage, present, ConstructionResult.finalState] using valid
  | some row =>
    simp only [landReceivingStorage, present]
    split <;> exact valid

private theorem construction_pure_bind (value : α) (next : α → ConstructionM β) :
    pure value >>= next = next value := rfl

private theorem construction_bind_assoc (action : ConstructionM α) (first : α → ConstructionM β)
    (next : β → ConstructionM γ) :
    (action >>= first) >>= next = action >>= fun value => first value >>= next := by
  funext state
  simp only [bind]
  cases action state <;> rfl

private theorem construction_if_bind (condition : Prop) [Decidable condition]
    (yes no : ConstructionM α) (next : α → ConstructionM β) :
    (if condition then yes else no) >>= next =
      if condition then yes >>= next else no >>= next := by
  by_cases selected : condition <;> simp [selected]

private theorem prefix_bind (action : ConstructionM α) (next : α → ConstructionM β)
    (first : (PreservesPrefixInvariant before) action)
    (remaining : ∀ value, (PreservesPrefixInvariant before) (next value)) :
    (PreservesPrefixInvariant before) (action >>= next) := by
  intro state valid
  have preserved := first state valid
  cases result : action state with
  | ok value after =>
      simp only [bind, result]
      exact remaining value after (by simpa only [result, ConstructionResult.finalState] using preserved)
  | fault kind after => simpa only [bind, result, ConstructionResult.finalState] using preserved

private theorem prefix_pure (value : α) : (PreservesPrefixInvariant before) (pure value) :=
  fun _ valid => valid

private theorem prefix_fail (kind : ConstructionFault) :
    (PreservesPrefixInvariant before) (ConstructionM.fail (α := α) kind) := fun _ valid => valid

private theorem prefix_fault_bind (kind : ConstructionFault) (next : α → ConstructionM β) :
    (PreservesPrefixInvariant before) (ConstructionM.fail kind >>= next) := fun _ valid => valid

private theorem prefix_if (condition : Prop) [Decidable condition] (yes no : ConstructionM α)
    (first : (PreservesPrefixInvariant before) yes) (second : (PreservesPrefixInvariant before) no) :
    (PreservesPrefixInvariant before) (if condition then yes else no) := by
  by_cases selected : condition
  · simpa only [selected, ↓reduceIte] using first
  · simpa only [selected, ↓reduceIte] using second

private theorem prefix_storage_lookup (id : StorageId) (action : ConstructionM ReceivingStorage)
    (result : ∀ state, action state = match state.storage[id]? with
      | some storage => .ok storage state
      | none => .fault .storage state) : (PreservesPrefixInvariant before) action := by
  intro state valid
  rw [result]
  cases state.storage[id]? <;> exact valid

private theorem prefix_storage_replace (id : StorageId) (storage : ReceivingStorage)
    (action : ConstructionM Unit)
    (result : ∀ state, action state = if id < state.storage.size then
      .ok () { state with storage := state.storage.set! id storage }
      else .fault .storage state) : (PreservesPrefixInvariant before) action := by
  intro state valid
  rw [result]
  split <;> exact valid

private theorem prefix_get_bind (next : ConstructionState → ConstructionM α)
    (safe : ∀ state, PrefixInvariant before state → (PrefixInvariant before) (next state state).finalState) :
    (PreservesPrefixInvariant before) (ConstructionM.get >>= next) := safe

private theorem prefix_get_snapshot_bind (next : ConstructionState → ConstructionM α)
    (safe : ∀ state, PrefixInvariant before state → (PreservesPrefixInvariant before) (next state)) :
    (PreservesPrefixInvariant before) (ConstructionM.get >>= next) := by
  intro state valid
  exact safe state valid state valid

private theorem prefix_set_state (updated : ConstructionState)
    (valid : (PrefixInvariant before) updated) :
    (PreservesPrefixInvariant before) (ConstructionM.set updated) := fun _ _ => valid

private theorem prefix_foreach (values : List α) (body : α → ConstructionM Unit)
    (safe : ∀ value, (PreservesPrefixInvariant before) (body value)) :
    (PreservesPrefixInvariant before) (do for value in values do body value) := by
  have loop : ∀ (remaining : List α) (inside : ∃ earlier, earlier ++ remaining = values),
      (PreservesPrefixInvariant before) (List.forIn'.loop values
        (fun value _ (_ : Unit) => do body value; pure (.yield ())) remaining () inside) := by
    intro remaining
    induction remaining with
    | nil => intro _; exact fun _ valid => valid
    | cons value rest ih =>
        intro inside
        simp only [List.forIn'.loop]
        apply prefix_bind
        · apply prefix_bind
          · exact safe value
          · intro _; exact fun _ valid => valid
        · intro step
          cases step with
          | done accumulator => exact fun _ valid => valid
          | yield accumulator => cases accumulator; exact ih _
  apply prefix_bind
  · exact loop values ⟨[], rfl⟩
  · intro _; exact fun _ valid => valid


private theorem prefix_lookup (id : DestinationId) (action : ConstructionM PendingDestination)
    (result : ∀ state, action state = match state.destinations[id]? with
      | some row => .ok row state | none => .fault .destination state) :
    (PreservesPrefixInvariant before) action := by
  intro state valid
  rw [result]
  cases state.destinations[id]? <;> exact valid

private theorem prefix_replace (id : DestinationId) (row : PendingDestination)
    (action : ConstructionM Unit)
    (result : ∀ state, action state = if id < state.destinations.size then
      .ok () { state with destinations := state.destinations.set! id row }
      else .fault .destination state) : (PreservesPrefixInvariant before) action := by
  intro state valid
  rw [result]
  split <;> simpa only [PrefixInvariant, ConstructionResult.finalState, Array.size_set!] using valid

set_option maxHeartbeats 800000 in
theorem releaseExitReservation_events_prefix (token : ExitReservationId) :
    (PreservesPrefixInvariant before) (releaseExitReservation token) := by
  unfold releaseExitReservation
  repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind]
    | with_reducible exact prefix_pure _
    | with_reducible exact prefix_fail _
    | with_reducible exact prefix_fault_bind _ _
    | with_reducible exact prefix_of_native _ (abandonTree_events_prefix _)
    | with_reducible exact prefix_lookup _ _ (lookupDestination_result _)
    | with_reducible exact prefix_replace _ _ _ (replaceDestination_result _ _)
    | with_reducible exact prefix_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact prefix_storage_replace _ _ _ (replaceStorage_result _ _)
    | solve
      | with_reducible apply prefix_set_state
        assumption
    | with_reducible apply prefix_get_snapshot_bind
    | with_reducible apply prefix_foreach
    | with_reducible apply prefix_bind
    | with_reducible apply prefix_if
    | assumption
    | dsimp only
    | split
    | intro value

set_option maxHeartbeats 800000 in
theorem markNamedReservation_events_prefix (token : ExitReservationId) :
    (PreservesPrefixInvariant before) (markNamedReservation token) := by
  unfold markNamedReservation
  repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind]
    | with_reducible exact prefix_pure _
    | with_reducible exact prefix_fail _
    | with_reducible exact prefix_fault_bind _ _
    | with_reducible exact prefix_of_native _ (abandonTree_events_prefix _)
    | with_reducible exact prefix_lookup _ _ (lookupDestination_result _)
    | with_reducible exact prefix_replace _ _ _ (replaceDestination_result _ _)
    | with_reducible exact prefix_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact prefix_storage_replace _ _ _ (replaceStorage_result _ _)
    | solve
      | with_reducible apply prefix_set_state
        assumption
    | with_reducible apply prefix_get_snapshot_bind
    | with_reducible apply prefix_foreach
    | with_reducible apply prefix_bind
    | with_reducible apply prefix_if
    | assumption
    | dsimp only
    | split
    | intro value

set_option maxHeartbeats 800000 in
theorem cancelExitReservation_events_prefix (token : ExitReservationId) (carried : List DestinationId) :
    (PreservesPrefixInvariant before) (cancelExitReservation token carried) := by
  unfold cancelExitReservation
  repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind]
    | with_reducible exact prefix_pure _
    | with_reducible exact prefix_fail _
    | with_reducible exact prefix_fault_bind _ _
    | with_reducible exact prefix_of_native _ (abandonTree_events_prefix _)
    | with_reducible exact prefix_lookup _ _ (lookupDestination_result _)
    | with_reducible exact prefix_replace _ _ _ (replaceDestination_result _ _)
    | with_reducible exact prefix_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact prefix_storage_replace _ _ _ (replaceStorage_result _ _)
    | solve
      | with_reducible apply prefix_set_state
        assumption
    | with_reducible apply prefix_get_snapshot_bind
    | with_reducible apply prefix_foreach
    | with_reducible apply prefix_bind
    | with_reducible apply prefix_if
    | assumption
    | dsimp only
    | split
    | intro value

set_option maxHeartbeats 800000 in
theorem restoreNamedDestination_events_prefix (id : DestinationId) :
    (PreservesPrefixInvariant before) (restoreNamedDestination id) := by
  unfold restoreNamedDestination
  repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind]
    | with_reducible exact prefix_pure _
    | with_reducible exact prefix_fail _
    | with_reducible exact prefix_fault_bind _ _
    | with_reducible exact prefix_of_native _ (abandonTree_events_prefix _)
    | with_reducible exact cancelExitReservation_events_prefix _ _
    | with_reducible exact prefix_lookup _ _ (lookupDestination_result _)
    | with_reducible exact prefix_replace _ _ _ (replaceDestination_result _ _)
    | with_reducible exact prefix_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact prefix_storage_replace _ _ _ (replaceStorage_result _ _)
    | solve
      | with_reducible apply prefix_set_state
        assumption
    | with_reducible apply prefix_get_snapshot_bind
    | with_reducible apply prefix_foreach
    | with_reducible apply prefix_bind
    | with_reducible apply prefix_if
    | assumption
    | dsimp only
    | split
    | intro value

set_option maxHeartbeats 800000 in
theorem materializeNamedReservation_events_prefix (token : ExitReservationId) :
    (PreservesPrefixInvariant before) (materializeNamedReservation token) := by
  unfold materializeNamedReservation
  repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind]
    | with_reducible exact prefix_pure _
    | with_reducible exact prefix_fail _
    | with_reducible exact prefix_fault_bind _ _
    | with_reducible exact prefix_of_native _ (abandonTree_events_prefix _)
    | with_reducible exact cancelExitReservation_events_prefix _ _
    | with_reducible exact restoreNamedDestination_events_prefix _
    | with_reducible exact prefix_lookup _ _ (lookupDestination_result _)
    | with_reducible exact prefix_replace _ _ _ (replaceDestination_result _ _)
    | with_reducible exact prefix_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact prefix_storage_replace _ _ _ (replaceStorage_result _ _)
    | solve
      | with_reducible apply prefix_set_state
        assumption
    | with_reducible apply prefix_get_snapshot_bind
    | with_reducible apply prefix_foreach
    | with_reducible apply prefix_bind
    | with_reducible apply prefix_if
    | assumption
    | dsimp only
    | split
    | intro value

local syntax "prefix_renew_split_if" : tactic
elab_rules : tactic
  | `(tactic| prefix_renew_split_if) =>
      Lean.Elab.Tactic.liftMetaTactic fun goal => do
        let some (yes, no) ← Lean.Meta.splitIfTarget? goal
          | Lean.throwError "no renewal condition to split"
        return [yes.mvarId, no.mvarId]


set_option maxHeartbeats 3000000 in
theorem renewReceivingDestination_events_prefix
    (incoming : DestinationId) (state : ConstructionState)
    (valid : (PrefixInvariant before) state) :
    (PrefixInvariant before) (renewReceivingDestination incoming state).finalState := by
  simp only [renewReceivingDestination, ConstructionM.get, bind]
  cases resolved : destinationCurrent state incoming with
  | error kind => exact valid
  | ok id =>
      simp only [pure, lookupDestination_result, bind]
      cases present : state.destinations[id]? with
      | none => exact valid
      | some destination =>
          simp only [present]
          cases progress : destination.progress <;> simp only [progress]
          all_goals try exact valid
          all_goals
            try simp only [ConstructionM.get, bind]
            cases saved : state.destinationResumptions.lookup id with
            | none => simp only [saved]; exact valid
            | some snapshot =>
                simp only [saved, lookupStorage_result, bind]
                cases stored : state.storage[snapshot.storage]? with
                | none => simp only [stored]; exact valid
                | some storage =>
                    simp only [stored]
                    have storageInside := (Array.getElem?_eq_some_iff.mp stored).choose
                    cases adaptation : snapshot.adaptation <;> simp only [adaptation]
                    all_goals
                      repeat' first
                        | exact valid
                        | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                            lookupDestination_result, replaceDestination_result, replaceStorage_result,
                            emit_result, pure, bind, ConstructionResult.finalState,
                            Array.size_push, Array.size_set!, List.append_assoc,
                            storageInside, ↓reduceIte]
                        | prefix_renew_split_if
                      all_goals
                        cases use : snapshot.use with
                        | receiver =>
                            simp only [use]
                            cases backing : snapshot.backing <;> simp only [backing]
                            all_goals
                              repeat' first
                                | exact valid
                                | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                                    replaceStorage_result, emit_result, pure, bind, ConstructionResult.finalState,
                                    Array.size_push, Array.size_set!, List.append_assoc,
                                    storageInside, ↓reduceIte]
                                | prefix_renew_split_if
                            all_goals
                              exact valid.trans (List.prefix_append _ _)
                        | child parent | replacement parent =>
                            simp only [use, lookupDestination_result, bind]
                            cases parentPresent : state.destinations[parent]? with
                            | none => simp only [parentPresent]; exact valid
                            | some owner =>
                                simp only [parentPresent]
                                have inside := (Array.getElem?_eq_some_iff.mp parentPresent).choose
                                have insideAfter := Nat.lt_succ_of_lt inside
                                cases ownerProgress : owner.progress <;> simp only [ownerProgress]
                                all_goals try exact valid
                                all_goals
                                  cases backing : snapshot.backing <;> simp only [backing]
                                  all_goals
                                    repeat' first
                                      | exact valid
                                      | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                                          replaceDestination_result, replaceStorage_result,
                                          emit_result, pure, bind, ConstructionResult.finalState,
                                          Array.size_push, Array.size_set!, List.append_assoc,
                                          storageInside, insideAfter, ↓reduceIte]
                                      | prefix_renew_split_if
                                  all_goals
                                    exact valid.trans (List.prefix_append _ _)

private theorem prefix_frontier (fuel : Nat) (id : DestinationId) :
    (PreservesPrefixInvariant before) (exitFrontierAction fuel id) := by
  intro state valid
  rw [exitFrontierAction_finalState]
  exact valid

private theorem prefix_anchor (fuel id storage : Nat) (receiving : Option DestinationId) :
    (PreservesPrefixInvariant before) (exitLandingAnchor fuel id storage receiving) := by
  intro state valid
  rw [exitLandingAnchor_finalState]
  exact valid

private theorem prefix_protected (action : List PendingDestination → ConstructionM Unit)
    (nilResult : ∀ state, action [] state = .ok () state)
    (consResult : ∀ row rest state, action (row :: rest) state =
      if row.capability.id < state.destinations.size then
        action rest { state with
          destinations := state.destinations.set! row.capability.id { row with progress := .abandoned }
          events := state.events ++ [.abandon row.capability.id] }
      else .fault .destination state) (rows : List PendingDestination) :
    (PreservesPrefixInvariant before) (action rows) := by
  intro state valid
  induction rows generalizing state with
  | nil => rw [nilResult]; exact valid
  | cons row rest ih =>
    rw [consResult]
    split
    · apply ih
      exact valid.trans (List.prefix_append _ _)
    · exact valid

private theorem prefix_emit (event : ConstructionEvent) (action : ConstructionM Unit)
    (result : ∀ state, action state = .ok () {state with events := state.events ++ [event]})
    : (PreservesPrefixInvariant before) action := by
  intro state valid
  rw [result]
  exact valid.trans (List.prefix_append _ _)

set_option maxHeartbeats 800000 in
theorem reserveExitDestination_events_prefix (incoming : DestinationId) (source : ExitSource) :
    (PreservesPrefixInvariant before) (reserveExitDestination incoming source) := by
  rw [reserveExitDestination_equation]
  repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind]
    | with_reducible exact prefix_pure _
    | with_reducible exact prefix_fail _
    | with_reducible exact prefix_fault_bind _ _
    | with_reducible exact renewReceivingDestination_events_prefix _
    | with_reducible exact prefix_of_native _ (openExitReplacement_events_prefix _)
    | with_reducible exact prefix_frontier _ _
    | with_reducible exact prefix_lookup _ _ (lookupDestination_result _)
    | with_reducible exact prefix_replace _ _ _ (replaceDestination_result _ _)
    | with_reducible exact prefix_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact prefix_storage_replace _ _ _ (replaceStorage_result _ _)
    | solve
      | with_reducible apply prefix_set_state
        assumption
    | with_reducible apply prefix_get_snapshot_bind
    | with_reducible apply prefix_foreach
    | with_reducible apply prefix_bind
    | with_reducible apply prefix_if
    | assumption
    | dsimp only
    | split
    | intro value

set_option maxHeartbeats 800000 in
theorem commitExitReplacement_events_prefix (receiving : Option DestinationId) (id : DestinationId) :
    (PreservesPrefixInvariant before) (commitExitReplacement receiving id) := by
  unfold commitExitReplacement
  repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind, landCompletedReplacement_transition]
    | with_reducible exact prefix_pure _
    | with_reducible exact prefix_fail _
    | with_reducible exact prefix_fault_bind _ _
    | with_reducible exact prefix_anchor _ _ _ _
    | with_reducible exact prefix_protected _ protectedAbandonment_nil_transition protectedAbandonment_cons_transition _
    | with_reducible exact prefix_landReceivingStorage _ _ _
    | with_reducible exact prefix_emit _ _ (emit_result _)
    | with_reducible exact prefix_lookup _ _ (lookupDestination_result _)
    | with_reducible exact prefix_replace _ _ _ (replaceDestination_result _ _)
    | with_reducible exact prefix_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact prefix_storage_replace _ _ _ (replaceStorage_result _ _)
    | solve
      | with_reducible apply prefix_set_state
        assumption
    | with_reducible apply prefix_get_snapshot_bind
    | with_reducible apply prefix_foreach
    | with_reducible apply prefix_bind
    | with_reducible apply prefix_if
    | assumption
    | dsimp only
    | split
    | intro value


theorem landExitReplacementChain_events_prefix (id : DestinationId) :
    (PreservesPrefixInvariant before) (landExitReplacementChain id) :=
  commitExitReplacement_events_prefix none id

theorem landExitReplacementInto_events_prefix (receiving id : DestinationId) :
    (PreservesPrefixInvariant before) (landExitReplacementInto receiving id) :=
  commitExitReplacement_events_prefix (some receiving) id

local syntax "reservation_owner_split_if" : tactic
elab_rules : tactic
  | `(tactic| reservation_owner_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal | Lean.throwError "no owner condition to split"
      return [yes.mvarId, no.mvarId]


theorem restoreCompletedOwner_events_prefix (snapshot : PendingDestination)
    (incoming : DestinationId) (carried : List DestinationId) :
    PreservesConstructionInvariant (PrefixInvariant before) (restoreCompletedOwner snapshot incoming carried) := by
  intro state valid
  simp only [restoreCompletedOwner]
  cases progress : snapshot.progress <;> try exact valid
  rename_i originalCount
  have receiving := stateQuery_receivingDestination incoming state
  cases resolved : receivingDestination incoming state with
  | stop reason after | escape target carriers after | jump target kind after =>
      simp only [resolved, Goose.Proofs.Exit.stepState] at receiving
      simpa only [resolved, bind, Goose.Proofs.Exit.stepState, receiving] using valid
  | ok current after =>
      simp only [resolved, Goose.Proofs.Exit.stepState] at receiving
      subst after
      simp only [resolved, bind, EvalM.get]
      split
      · exact valid
      · cases childFound : state.construction.destinations[current]? with
        | none => simpa only [getDestination, EvalM.get, bind, childFound, Construct.fault, EvalM.stop, Goose.Proofs.Exit.stepState] using valid
        | some child =>
            cases parentFound : state.construction.destinations[snapshot.capability.id]? with
            | none => simpa only [getDestination, EvalM.get, bind, childFound, pure, parentFound, Construct.fault, EvalM.stop, Goose.Proofs.Exit.stepState] using valid
            | some parent =>
                simp only [getDestination, EvalM.get, bind, childFound, parentFound, pure]
                cases parentProgress : parent.progress <;> cases childProgress : child.progress <;>
                  try exact valid
                all_goals
                  rename_i count expected
                  simp only []
                  reservation_owner_split_if
                  · simpa only [Construct.fault, EvalM.stop, bind, Goose.Proofs.Exit.stepState] using valid
                  · rename_i guard
                    simp only [EvalM.get, EvalM.set, bind, pure, Goose.Proofs.Exit.stepState]
                    simpa only [ExecutionInvariant, PrefixInvariant, Array.size_set!] using valid

theorem waitExitDestination_events_prefix (incoming : DestinationId) :
    (PreservesPrefixInvariant before) (waitExitDestination incoming) := by
  intro state valid
  exact valid

theorem selectWaitingExitDestination_events_prefix (token : ExitReservationId) (source : ExitSource) :
    (PreservesPrefixInvariant before) (selectWaitingExitDestination token source) := by
  intro state valid
  simp only [selectWaitingExitDestination, ConstructionM.get, bind]
  cases present : state.exitReservations[token]? with
  | none => exact valid
  | some reservation =>
      cases reservation with
      | active role incoming selected snapshot | restored | released => exact valid
      | waiting incoming =>
          have reserved := reserveExitDestination_events_prefix incoming source state valid
          cases prepared : prepareExitDestinationAction incoming source state with
          | fault reason after =>
              simpa only [reserveExitDestination, prepared, bind, ConstructionResult.finalState] using reserved
          | ok pair after =>
              rcases pair with ⟨selected, snapshot⟩
              simpa only [reserveExitDestination, prepared, bind, ConstructionM.get, ConstructionM.set, pure,
                ConstructionResult.finalState, PrefixInvariant] using reserved

def eventPrefixReservationPrimitives : ConstructionReservationPrimitives (PrefixInvariant before) where
  restoreOwner := restoreCompletedOwner_events_prefix
  preserves := by
    intro α action primitive
    cases primitive with
    | reserveExitDestination incoming source => exact reserveExitDestination_events_prefix incoming source
    | waitExitDestination incoming => exact waitExitDestination_events_prefix incoming
    | selectWaitingExitDestination token source => exact selectWaitingExitDestination_events_prefix token source
    | rearmExitReservation borrowed => exact rearmExitReservation_events_prefix borrowed
    | markNamedReservation token => exact markNamedReservation_events_prefix token
    | materializeNamedReservation token => exact materializeNamedReservation_events_prefix token
    | renewReceivingDestination incoming => exact renewReceivingDestination_events_prefix incoming
    | releaseExitReservation token => exact releaseExitReservation_events_prefix token
    | cancelExitReservation token carried => exact cancelExitReservation_events_prefix token carried
    | landExitReplacementChain id => exact landExitReplacementChain_events_prefix id
    | landExitReplacementInto receiving id => exact landExitReplacementInto_events_prefix receiving id

end Goose.Proofs.ConstructionExecutionEventPrefixProtocol
