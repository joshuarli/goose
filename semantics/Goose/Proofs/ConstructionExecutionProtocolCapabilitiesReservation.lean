import Goose.Construct.Destination
import Goose.Proofs.ConstructionExecutionProtocolQueries
import Goose.Proofs.ConstructionExecutionProtocolReservationKernel
import Lean.Elab.Tactic.Split
import Goose.Proofs.ConstructionExecutionProtocolReservationFrontier
import Goose.Proofs.ConstructionExecutionProtocolReservationRearm

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

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

private theorem capabilities_push (state : ConstructionState) (destination : PendingDestination)
    (valid : DestinationCapabilitiesIndexed state)
    (correct : destination.capability.id = state.destinations.size) :
    DestinationCapabilitiesIndexed { state with destinations := state.destinations.push destination } := by
  intro index stored present
  simp only [Array.getElem?_push] at present
  by_cases same : index = state.destinations.size
  · simp only [same, ↓reduceIte] at present
    cases present
    exact correct.trans same.symm
  · exact valid index stored (by simpa only [same, ↓reduceIte] using present)

private theorem capabilities_set (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (valid : DestinationCapabilitiesIndexed state)
    (correct : destination.capability.id = id) :
    DestinationCapabilitiesIndexed { state with destinations := state.destinations.set! id destination } := by
  intro index stored present
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at present
  by_cases same : id = index
  · subst index
    by_cases inside : id < state.destinations.size
    · simp only [↓reduceIte, inside] at present
      cases present
      exact correct
    · simp [inside] at present
  · exact valid index stored (by simpa only [same, ↓reduceIte] using present)

private theorem capabilities_bind (action : ConstructionM α) (next : α → ConstructionM β)
    (first : PreservesDestinationCapabilities action)
    (remaining : ∀ value, PreservesDestinationCapabilities (next value)) :
    PreservesDestinationCapabilities (action >>= next) := by
  intro state valid
  have preserved := first state valid
  cases result : action state with
  | ok value after =>
      simp only [bind, result]
      exact remaining value after (by simpa only [result, ConstructionResult.finalState] using preserved)
  | fault kind after => simpa only [bind, result, ConstructionResult.finalState] using preserved

private theorem capabilities_pure (value : α) : PreservesDestinationCapabilities (pure value) :=
  fun _ valid => valid

private theorem capabilities_fail (kind : ConstructionFault) :
    PreservesDestinationCapabilities (ConstructionM.fail (α := α) kind) := fun _ valid => valid

private theorem capabilities_fault_bind (kind : ConstructionFault) (next : α → ConstructionM β) :
    PreservesDestinationCapabilities (ConstructionM.fail kind >>= next) := fun _ valid => valid

private theorem capabilities_if (condition : Prop) [Decidable condition] (yes no : ConstructionM α)
    (first : PreservesDestinationCapabilities yes) (second : PreservesDestinationCapabilities no) :
    PreservesDestinationCapabilities (if condition then yes else no) := by
  by_cases selected : condition
  · simpa only [selected, ↓reduceIte] using first
  · simpa only [selected, ↓reduceIte] using second

private theorem capabilities_lookup_bind (id : DestinationId) (action : ConstructionM PendingDestination)
    (result : ∀ state, action state = match state.destinations[id]? with
      | some destination => .ok destination state
      | none => .fault .destination state)
    (next : PendingDestination → ConstructionM α)
    (safe : ∀ destination, destination.capability.id = id → PreservesDestinationCapabilities (next destination)) :
    PreservesDestinationCapabilities (action >>= next) := by
  intro state valid
  simp only [bind, result]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some destination => exact safe destination (valid id destination present) state valid

private theorem capabilities_replace (id : DestinationId) (destination : PendingDestination)
    (action : ConstructionM Unit)
    (result : ∀ state, action state = if id < state.destinations.size then
      .ok () { state with destinations := state.destinations.set! id destination }
      else .fault .destination state)
    (correct : destination.capability.id = id) : PreservesDestinationCapabilities action := by
  intro state valid
  simp only [result]
  split
  · exact capabilities_set state id destination valid correct
  · exact valid

private theorem capabilities_storage_lookup (id : StorageId) (action : ConstructionM ReceivingStorage)
    (result : ∀ state, action state = match state.storage[id]? with
      | some storage => .ok storage state
      | none => .fault .storage state) : PreservesDestinationCapabilities action := by
  intro state valid
  rw [result]
  cases state.storage[id]? <;> exact valid

private theorem capabilities_storage_replace (id : StorageId) (storage : ReceivingStorage)
    (action : ConstructionM Unit)
    (result : ∀ state, action state = if id < state.storage.size then
      .ok () { state with storage := state.storage.set! id storage }
      else .fault .storage state) : PreservesDestinationCapabilities action := by
  intro state valid
  rw [result]
  split <;> exact valid

private theorem capabilities_emit (event : ConstructionEvent) (action : ConstructionM Unit)
    (result : ∀ state, action state = .ok () { state with events := state.events ++ [event] }) :
    PreservesDestinationCapabilities action := by
  intro state valid
  rw [result]
  exact valid

private theorem capabilities_get_bind (next : ConstructionState → ConstructionM α)
    (safe : ∀ state, DestinationCapabilitiesIndexed state → DestinationCapabilitiesIndexed (next state state).finalState) :
    PreservesDestinationCapabilities (ConstructionM.get >>= next) := safe

private theorem capabilities_get_snapshot_bind (next : ConstructionState → ConstructionM α)
    (safe : ∀ state, DestinationCapabilitiesIndexed state → PreservesDestinationCapabilities (next state)) :
    PreservesDestinationCapabilities (ConstructionM.get >>= next) := by
  intro state valid
  exact safe state valid state valid

private theorem capabilities_set_state (updated : ConstructionState)
    (valid : DestinationCapabilitiesIndexed updated) :
    PreservesDestinationCapabilities (ConstructionM.set updated) := fun _ _ => valid

private theorem capabilities_foreach (values : List α) (body : α → ConstructionM Unit)
    (safe : ∀ value, PreservesDestinationCapabilities (body value)) :
    PreservesDestinationCapabilities (do for value in values do body value) := by
  have loop : ∀ (remaining : List α) (inside : ∃ earlier, earlier ++ remaining = values),
      PreservesDestinationCapabilities (List.forIn'.loop values
        (fun value _ (_ : Unit) => do body value; pure (.yield ())) remaining () inside) := by
    intro remaining
    induction remaining with
    | nil => intro _; exact fun _ valid => valid
    | cons value rest ih =>
        intro inside
        simp only [List.forIn'.loop]
        apply capabilities_bind
        · apply capabilities_bind
          · exact safe value
          · intro _; exact fun _ valid => valid
        · intro step
          cases step with
          | done accumulator => exact fun _ valid => valid
          | yield accumulator => cases accumulator; exact ih _
  apply capabilities_bind
  · exact loop values ⟨[], rfl⟩
  · intro _; exact fun _ valid => valid


set_option maxHeartbeats 800000 in
theorem releaseExitReservation_destination_capabilities (token : ExitReservationId) :
    PreservesDestinationCapabilities (releaseExitReservation token) := by
  unfold releaseExitReservation
  repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind]
    | with_reducible exact capabilities_pure _
    | with_reducible exact capabilities_fail _
    | with_reducible exact capabilities_fault_bind _ _
    | with_reducible exact abandonTree_destination_capabilities _
    | with_reducible exact capabilities_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact capabilities_storage_replace _ _ _ (replaceStorage_result _ _)
    | solve
      | with_reducible apply capabilities_replace _ _ _ (replaceDestination_result _ _)
        first | assumption | rfl
    | solve
      | with_reducible apply capabilities_set_state
        assumption
    | with_reducible apply capabilities_lookup_bind _ _ (lookupDestination_result _)
    | with_reducible apply capabilities_get_snapshot_bind
    | with_reducible apply capabilities_bind
    | with_reducible apply capabilities_if
    | assumption
    | dsimp only
    | split
    | intro value

set_option maxHeartbeats 800000 in
theorem markNamedReservation_destination_capabilities (token : ExitReservationId) :
    PreservesDestinationCapabilities (markNamedReservation token) := by
  unfold markNamedReservation
  repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind]
    | with_reducible exact capabilities_pure _
    | with_reducible exact capabilities_fail _
    | with_reducible exact capabilities_fault_bind _ _
    | with_reducible exact abandonTree_destination_capabilities _
    | with_reducible exact capabilities_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact capabilities_storage_replace _ _ _ (replaceStorage_result _ _)
    | solve
      | with_reducible apply capabilities_replace _ _ _ (replaceDestination_result _ _)
        first | assumption | rfl
    | solve
      | with_reducible apply capabilities_set_state
        assumption
    | with_reducible apply capabilities_lookup_bind _ _ (lookupDestination_result _)
    | with_reducible apply capabilities_get_snapshot_bind
    | with_reducible apply capabilities_bind
    | with_reducible apply capabilities_if
    | assumption
    | dsimp only
    | split
    | intro value

set_option maxHeartbeats 800000 in
theorem cancelExitReservation_destination_capabilities (token : ExitReservationId) (carried : List DestinationId) :
    PreservesDestinationCapabilities (cancelExitReservation token carried) := by
  unfold cancelExitReservation
  repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind]
    | with_reducible exact capabilities_pure _
    | with_reducible exact capabilities_fail _
    | with_reducible exact capabilities_fault_bind _ _
    | with_reducible exact abandonTree_destination_capabilities _
    | with_reducible exact capabilities_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact capabilities_storage_replace _ _ _ (replaceStorage_result _ _)
    | solve
      | with_reducible apply capabilities_replace _ _ _ (replaceDestination_result _ _)
        first | assumption | rfl
    | solve
      | with_reducible apply capabilities_set_state
        assumption
    | with_reducible apply capabilities_lookup_bind _ _ (lookupDestination_result _)
    | with_reducible apply capabilities_get_snapshot_bind
    | with_reducible apply capabilities_bind
    | with_reducible apply capabilities_if
    | assumption
    | dsimp only
    | split
    | intro value

set_option maxHeartbeats 800000 in
theorem renewReceivingDestination_destination_capabilities (incoming : DestinationId) :
    PreservesDestinationCapabilities (renewReceivingDestination incoming) := by
  unfold renewReceivingDestination
  repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind]
    | with_reducible exact capabilities_pure _
    | with_reducible exact capabilities_fail _
    | with_reducible exact capabilities_fault_bind _ _
    | with_reducible exact abandonTree_destination_capabilities _
    | with_reducible exact capabilities_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact capabilities_storage_replace _ _ _ (replaceStorage_result _ _)
    | solve
      | with_reducible apply capabilities_replace _ _ _ (replaceDestination_result _ _)
        first | assumption | rfl
    | solve
      | with_reducible apply capabilities_set_state
        assumption
    | solve
      | with_reducible apply capabilities_set_state
        intro index stored present
        exact capabilities_push _ _ (by assumption) rfl index stored present
    | with_reducible apply capabilities_lookup_bind _ _ (lookupDestination_result _)
    | with_reducible apply capabilities_get_snapshot_bind
    | with_reducible apply capabilities_bind
    | with_reducible apply capabilities_if
    | assumption
    | dsimp only
    | split
    | intro value

private theorem capabilities_frontier (fuel : Nat) (id : DestinationId) :
    PreservesDestinationCapabilities (exitFrontierAction fuel id) := by
  intro state valid
  rw [exitFrontierAction_finalState]
  exact valid

set_option maxHeartbeats 800000 in
theorem reserveExitDestination_destination_capabilities (incoming : DestinationId) (source : ExitSource) :
    PreservesDestinationCapabilities (reserveExitDestination incoming source) := by
  rw [reserveExitDestination, prepareExitDestination_equation]
  repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind]
    | with_reducible exact capabilities_pure _
    | with_reducible exact capabilities_fail _
    | with_reducible exact capabilities_fault_bind _ _
    | with_reducible exact renewReceivingDestination_destination_capabilities _
    | with_reducible exact openExitReplacement_destination_capabilities _
    | with_reducible exact capabilities_frontier _ _
    | with_reducible exact capabilities_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact capabilities_storage_replace _ _ _ (replaceStorage_result _ _)
    | solve
      | with_reducible apply capabilities_replace _ _ _ (replaceDestination_result _ _)
        first | assumption | rfl
    | solve
      | with_reducible apply capabilities_set_state
        assumption
    | with_reducible apply capabilities_lookup_bind _ _ (lookupDestination_result _)
    | with_reducible apply capabilities_get_snapshot_bind
    | with_reducible apply capabilities_bind
    | with_reducible apply capabilities_if
    | assumption
    | dsimp only
    | split
    | intro value


set_option maxHeartbeats 800000 in
theorem selectWaitingExitDestination_destination_capabilities (token : ExitReservationId) (source : ExitSource) :
    PreservesDestinationCapabilities (selectWaitingExitDestination token source) := by
  unfold selectWaitingExitDestination
  repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind,
        prepareExitDestination_equation]
    | with_reducible exact capabilities_pure _
    | with_reducible exact capabilities_fail _
    | with_reducible exact capabilities_fault_bind _ _
    | with_reducible exact renewReceivingDestination_destination_capabilities _
    | with_reducible exact openExitReplacement_destination_capabilities _
    | with_reducible exact capabilities_frontier _ _
    | with_reducible exact capabilities_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact capabilities_storage_replace _ _ _ (replaceStorage_result _ _)
    | solve
      | with_reducible apply capabilities_replace _ _ _ (replaceDestination_result _ _)
        first | assumption | rfl
    | solve
      | with_reducible apply capabilities_set_state
        assumption
    | with_reducible apply capabilities_lookup_bind _ _ (lookupDestination_result _)
    | with_reducible apply capabilities_get_snapshot_bind
    | with_reducible apply capabilities_bind
    | with_reducible apply capabilities_if
    | assumption
    | dsimp only
    | split
    | intro value


theorem waitExitDestination_destination_capabilities (incoming : DestinationId) :
    PreservesDestinationCapabilities (waitExitDestination incoming) := by
  intro state valid
  exact valid




private theorem snapshot_capability_id (before after : PendingDestination) (id : DestinationId)
    (correct : before.capability.id = id)
    (allowed : ¬ ({before with progress := after.progress} != after) = true) :
    after.capability.id = id := by
  have same : {before with progress := after.progress} = after := by
    apply Classical.byContradiction
    intro different
    exact allowed (by simp [different])
  exact (congrArg (fun row : PendingDestination => row.capability.id) same).symm.trans correct


set_option maxHeartbeats 800000 in
theorem restoreNamedDestination_destination_capabilities (id : DestinationId) :
    PreservesDestinationCapabilities (restoreNamedDestination id) := by
  unfold restoreNamedDestination
  repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind]
    | with_reducible exact capabilities_pure _
    | with_reducible exact capabilities_fail _
    | with_reducible exact capabilities_fault_bind _ _
    | with_reducible exact abandonTree_destination_capabilities _
    | with_reducible exact cancelExitReservation_destination_capabilities _ _
    | with_reducible exact capabilities_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact capabilities_storage_replace _ _ _ (replaceStorage_result _ _)
    | solve
      | with_reducible apply capabilities_replace _ _ _ (replaceDestination_result _ _)
        first | assumption | rfl
    | solve
      | with_reducible apply capabilities_set_state
        assumption
    | with_reducible apply capabilities_lookup_bind _ _ (lookupDestination_result _)
    | with_reducible apply capabilities_get_snapshot_bind
    | with_reducible apply capabilities_foreach
    | with_reducible apply capabilities_bind
    | with_reducible apply capabilities_if
    | assumption
    | dsimp only
    | split
    | intro value


private theorem capabilities_if_guard (condition : Prop) [Decidable condition]
    (yes no : ConstructionM α)
    (first : condition → PreservesDestinationCapabilities yes)
    (second : ¬ condition → PreservesDestinationCapabilities no) :
    PreservesDestinationCapabilities (if condition then yes else no) := by
  by_cases selected : condition
  · simpa only [selected, ↓reduceIte] using first selected
  · simpa only [selected, ↓reduceIte] using second selected

set_option maxHeartbeats 800000 in
theorem materializeNamedReservation_destination_capabilities (token : ExitReservationId) :
    PreservesDestinationCapabilities (materializeNamedReservation token) := by
  unfold materializeNamedReservation
  repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind]
    | with_reducible exact capabilities_pure _
    | with_reducible exact capabilities_fail _
    | with_reducible exact capabilities_fault_bind _ _
    | with_reducible exact restoreNamedDestination_destination_capabilities _
    | with_reducible exact abandonTree_destination_capabilities _
    | with_reducible exact cancelExitReservation_destination_capabilities _ _
    | with_reducible exact capabilities_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact capabilities_storage_replace _ _ _ (replaceStorage_result _ _)
    | solve
      | with_reducible apply capabilities_replace _ _ _ (replaceDestination_result _ _)
        first | assumption | rfl | (apply snapshot_capability_id; assumption; assumption)
    | solve
      | with_reducible apply capabilities_set_state
        assumption
    | with_reducible apply capabilities_lookup_bind _ _ (lookupDestination_result _)
    | with_reducible apply capabilities_get_snapshot_bind
    | with_reducible apply capabilities_foreach
    | with_reducible apply capabilities_if_guard
    | with_reducible apply capabilities_bind
    | assumption
    | dsimp only
    | split
    | intro value


private theorem capabilities_anchor (fuel id storage : Nat) (receiving : Option DestinationId) :
    PreservesDestinationCapabilities (exitLandingAnchor fuel id storage receiving) := by
  intro state valid
  rw [exitLandingAnchor_finalState]
  exact valid

set_option maxHeartbeats 800000 in
theorem commitExitReplacement_destination_capabilities (receiving : Option DestinationId) (id : DestinationId) :
    PreservesDestinationCapabilities (commitExitReplacement receiving id) := by
  unfold commitExitReplacement
  repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind, landCompletedReplacement_transition]
    | with_reducible exact capabilities_pure _
    | with_reducible exact capabilities_fail _
    | with_reducible exact capabilities_fault_bind _ _
    | with_reducible exact capabilities_anchor _ _ _ _
    | with_reducible exact protectedAbandonment_destination_capabilities _
    | with_reducible exact landReceivingStorage_destination_capabilities _ _ _
    | with_reducible exact capabilities_emit _ _ (emit_result _)
    | with_reducible exact capabilities_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact capabilities_storage_replace _ _ _ (replaceStorage_result _ _)
    | solve
      | with_reducible apply capabilities_replace _ _ _ (replaceDestination_result _ _)
        first | assumption | rfl
    | solve
      | with_reducible apply capabilities_set_state
        assumption
    | with_reducible apply capabilities_lookup_bind _ _ (lookupDestination_result _)
    | with_reducible apply capabilities_get_snapshot_bind
    | with_reducible apply capabilities_bind
    | with_reducible apply capabilities_if
    | assumption
    | dsimp only
    | split
    | intro value


theorem landExitReplacementChain_destination_capabilities (id : DestinationId) :
    PreservesDestinationCapabilities (landExitReplacementChain id) :=
  commitExitReplacement_destination_capabilities none id

theorem landExitReplacementInto_destination_capabilities (receiving id : DestinationId) :
    PreservesDestinationCapabilities (landExitReplacementInto receiving id) :=
  commitExitReplacement_destination_capabilities (some receiving) id

local syntax "reservation_owner_split_if" : tactic
elab_rules : tactic
  | `(tactic| reservation_owner_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal | Lean.throwError "no owner condition to split"
      return [yes.mvarId, no.mvarId]


theorem restoreCompletedOwner_destination_capabilities (snapshot : PendingDestination)
    (incoming : DestinationId) (carried : List DestinationId) :
    PreservesConstructionInvariant DestinationCapabilitiesIndexed (restoreCompletedOwner snapshot incoming carried) := by
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
                    exact capabilities_set state.construction snapshot.capability.id snapshot valid rfl

theorem destinationCapabilitiesReservationPrimitives :
    ConstructionReservationPrimitives DestinationCapabilitiesIndexed where
  restoreOwner := restoreCompletedOwner_destination_capabilities
  preserves := by
    intro α action primitive
    cases primitive with
    | reserveExitDestination incoming source => exact reserveExitDestination_destination_capabilities incoming source
    | waitExitDestination incoming => exact waitExitDestination_destination_capabilities incoming
    | selectWaitingExitDestination token source => exact selectWaitingExitDestination_destination_capabilities token source
    | rearmExitReservation borrowed => exact rearmExitReservation_destination_capabilities borrowed
    | markNamedReservation token => exact markNamedReservation_destination_capabilities token
    | materializeNamedReservation token => exact materializeNamedReservation_destination_capabilities token
    | renewReceivingDestination incoming => exact renewReceivingDestination_destination_capabilities incoming
    | releaseExitReservation token => exact releaseExitReservation_destination_capabilities token
    | cancelExitReservation token carried => exact cancelExitReservation_destination_capabilities token carried
    | landExitReplacementChain id => exact landExitReplacementChain_destination_capabilities id
    | landExitReplacementInto receiving id => exact landExitReplacementInto_destination_capabilities receiving id

end Goose.Proofs.ConstructionExecutionProtocol
