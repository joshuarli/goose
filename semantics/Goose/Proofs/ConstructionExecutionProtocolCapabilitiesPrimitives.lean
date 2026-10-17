import Goose.Construct.Destination

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

private theorem capabilities_writable_bind (id : DestinationId) (action : ConstructionM PendingDestination)
    (result : ∀ state, action state = match state.destinations[id]? with
      | none => .fault .destination state
      | some destination => match destinationCanWrite state id with
        | true => .ok destination state
        | false => .fault .protocol state)
    (next : PendingDestination → ConstructionM α)
    (safe : ∀ destination, destination.capability.id = id → PreservesDestinationCapabilities (next destination)) :
    PreservesDestinationCapabilities (action >>= next) := by
  intro state valid
  simp only [bind, result]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some destination =>
      cases destinationCanWrite state id with
      | false => exact valid
      | true => exact safe destination (valid id destination present) state valid

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

set_option maxRecDepth 4096 in
theorem openDestination_destination_capabilities (storageId : StorageId)
    (capability : Goose.Core.Destination Goose.Construct.Ty) (layout : ReceivingLayout) (knownCount : Option Nat) :
    PreservesDestinationCapabilities (openDestination storageId capability layout knownCount) := by
  cases layout <;> cases knownCount
  all_goals rw [openDestination_transition]
  all_goals repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind]
    | with_reducible exact capabilities_pure _
    | with_reducible exact capabilities_fail _
    | with_reducible exact capabilities_fault_bind _ _
    | with_reducible exact reserveStorage_destination_capabilities _ _
    | with_reducible exact capabilities_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact capabilities_storage_replace _ _ _ (replaceStorage_result _ _)
    | with_reducible exact capabilities_emit _ _ (emit_result _)
    | solve
      | with_reducible apply capabilities_set_state
        with_reducible apply capabilities_push
        · assumption
        · rfl
    | with_reducible apply capabilities_get_snapshot_bind
    | with_reducible apply capabilities_bind
    | with_reducible apply capabilities_if
    | assumption
    | dsimp only
    | intro value

set_option maxRecDepth 4096 in
theorem openDestinationDirect_destination_capabilities (storageId : StorageId)
    (capability : Goose.Core.Destination Goose.Construct.Ty) (layout : ReceivingLayout) (knownCount : Option Nat) :
    PreservesDestinationCapabilities (openDestinationDirect storageId capability layout knownCount) := by
  cases layout <;> cases knownCount
  all_goals rw [openDestinationDirect_transition]
  all_goals repeat' first
    | simp only [construction_pure_bind, construction_bind_assoc, construction_if_bind]
    | with_reducible exact capabilities_pure _
    | with_reducible exact capabilities_fail _
    | with_reducible exact capabilities_fault_bind _ _
    | with_reducible exact reserveStorage_destination_capabilities _ _
    | with_reducible exact capabilities_storage_lookup _ _ (lookupStorage_result _)
    | with_reducible exact capabilities_storage_replace _ _ _ (replaceStorage_result _ _)
    | with_reducible exact capabilities_emit _ _ (emit_result _)
    | solve
      | with_reducible apply capabilities_set_state
        with_reducible apply capabilities_push
        · assumption
        · rfl
    | with_reducible apply capabilities_get_snapshot_bind
    | with_reducible apply capabilities_bind
    | with_reducible apply capabilities_if
    | assumption
    | dsimp only
    | intro value

set_option maxHeartbeats 400000 in
theorem publishOperation_destination_capabilities (ids : List DestinationId) :
    PreservesDestinationCapabilities (publishOperation ids) := by
  unfold publishOperation
  apply capabilities_get_bind
  intro state valid
  cases decision : preflightPublication state ids with
  | error reason => exact valid
  | ok result =>
    cases result
    dsimp only
    apply capabilities_foreach ids _ _ state valid
    intro id
    rw [publishReady_transition]
    repeat' first
      | with_reducible exact capabilities_pure _
      | with_reducible exact capabilities_fail _
      | with_reducible exact capabilities_fault_bind _ _
      | with_reducible exact capabilities_storage_lookup _ _ (lookupStorage_result _)
      | with_reducible exact capabilities_storage_replace _ _ _ (replaceStorage_result _ _)
      | with_reducible exact capabilities_emit _ _ (emit_result _)
      | solve
        | with_reducible apply capabilities_replace _ _ _ (replaceDestination_result _ _)
          first | assumption | rfl
      | with_reducible apply capabilities_writable_bind _ _ (writableDestination_result _)
      | with_reducible apply capabilities_lookup_bind _ _ (lookupDestination_result _)
      | with_reducible apply capabilities_bind
      | with_reducible apply capabilities_if
      | assumption
      | dsimp only
      | split
      | intro value


end Goose.Proofs.ConstructionExecutionProtocol
