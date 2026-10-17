import Goose.Proofs.ConstructionExecutionProtocolCleanup
import Goose.Proofs.ConstructionExecutionProtocolOwners

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

private abbrev writableStep (id : DestinationId) : ConstructionM PendingDestination := fun state =>
  (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left)
    (writableDestination_result id state)

private abbrev replaceStep (id : DestinationId) (destination : PendingDestination) : ConstructionM Unit := fun state =>
  (fun {left right : ConstructionResult Unit} (_ : left = right) => left)
    (replaceDestination_result id destination state)

private abbrev treeStep (destination : PendingDestination) : ConstructionM Unit := do
  let current ← writableStep destination.capability.id
  match current.progress with
  | .suspended count _ => replaceStep current.capability.id { current with progress := .open count }
  | _ => pure ()
  abandonDestination destination.capability.id

private theorem treeStep_preserves (destination : PendingDestination) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (treeStep destination state).finalState := by
  simp only [treeStep, writableStep, writableDestination_result, bind]
  cases present : state.destinations[destination.capability.id]? with
  | none => exact valid
  | some current =>
      simp only [present]
      cases allowed : destinationCanWrite state destination.capability.id with
      | false => exact valid
      | true =>
          simp only [allowed]
          have correct := valid.2.1 destination.capability.id current present
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          cases progress : current.progress <;> try simp only [progress] <;>
            try exact abandonDestination_destination_lifecycle_invariant destination.capability.id state valid
          case suspended count child =>
            have storageInside := (valid.2.2.1 destination.capability.id current present).1
            have remains := destinationCanWrite_replace_progress state destination.capability.id current (.open count)
              present valid.2.2.2
            simp only [Array.set!_eq_setIfInBounds] at remains
            simp only [replaceStep, correct, replaceDestination_result, inside, ↓reduceIte,
              abandonDestination, writableDestination_result, bind, Array.set!_eq_setIfInBounds,
              Array.getElem?_setIfInBounds_self_of_lt inside, remains, allowed]
            simp only [lookupStorage_result, bind]
            cases stored : state.storage[current.storage]? with
            | none =>
                exact False.elim (Nat.not_le_of_lt storageInside (Array.getElem?_eq_none_iff.mp stored))
            | some storage =>
                simp only [PendingDestination.storage] at stored storageInside
                simp only [PendingDestination.storage, stored, bind, replaceStorage_result, replaceDestination_result,
                  storageInside, Array.size_setIfInBounds, inside, ↓reduceIte,
                  Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds,
                  emit_result, ConstructionResult.finalState]
                apply destinationLifecycleInvariant_abandon_row
                  { state with storage := (state.storage.set! current.storage
                    { storage with bytes := storage.bytes.extract 0 current.rollbackEnd }) }
                  destination.capability.id current present
                · exact ⟨count, Or.inr (Or.inr (Or.inl ⟨child, progress⟩))⟩
                · apply destinationLifecycleInvariant_storage_frame state _ _ valid
                  simp

private abbrev treeForInStep (destination : PendingDestination) (_ : PUnit) :
    ConstructionM (ForInStep PUnit) := do
  let current ← writableStep destination.capability.id
  match current.progress with
  | .suspended count _ =>
      replaceStep current.capability.id { current with progress := .open count }
      abandonDestination destination.capability.id
      pure (.yield ⟨⟩)
  | _ =>
      abandonDestination destination.capability.id
      pure (.yield ⟨⟩)

private theorem treeForInStep_preserves (destination : PendingDestination) (token : PUnit)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (treeForInStep destination token state).finalState := by
  have equivalent : treeForInStep destination token =
      treeStep destination >>= fun _ => pure (.yield (PUnit.unit)) := by
    funext initial
    simp only [treeForInStep, treeStep, bind]
    cases result : writableStep destination.capability.id initial with
    | fault kind after => rfl
    | ok current after =>
        cases progress : current.progress <;> simp only [progress] <;> try rfl
        case suspended count child =>
          try simp only [bind]
          cases replaceStep current.capability.id {current with progress := .open count} after <;> rfl
  rw [equivalent]
  have preserved := treeStep_preserves destination state valid
  cases result : treeStep destination state <;>
    simpa only [bind, pure, result, ConstructionResult.finalState] using preserved

private theorem invariant_forIn (rows : List PendingDestination)
    (body : PendingDestination → PUnit → ConstructionM (ForInStep PUnit))
    (safe : ∀ destination token state, DestinationLifecycleInvariant state →
      DestinationLifecycleInvariant (body destination token state).finalState)
    (token : PUnit) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant ((forIn rows token body : ConstructionM PUnit) state).finalState := by
  induction rows generalizing token state with
  | nil => exact valid
  | cons destination rest ih =>
      have preserved := safe destination token state valid
      cases result : body destination token state with
      | fault kind after =>
          simpa only [List.forIn_cons, bind, result, ConstructionResult.finalState] using preserved
      | ok step after =>
          rw [result] at preserved
          cases step with
          | done token =>
              simpa only [List.forIn_cons, bind, pure, result, ConstructionResult.finalState] using preserved
          | yield token =>
              simpa only [List.forIn_cons, bind, result] using ih token after preserved

private theorem lifecycle_bind (action : ConstructionM α) (next : α → ConstructionM β)
    (first : ∀ state, DestinationLifecycleInvariant state →
      DestinationLifecycleInvariant (action state).finalState)
    (remaining : ∀ value state, DestinationLifecycleInvariant state →
      DestinationLifecycleInvariant (next value state).finalState)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant ((action >>= next) state).finalState := by
  have preserved := first state valid
  cases result : action state with
  | fault kind after => simpa only [bind, result, ConstructionResult.finalState] using preserved
  | ok value after =>
      rw [result] at preserved
      simpa only [bind, result] using remaining value after preserved

set_option maxHeartbeats 1000000 in
theorem abandonTree_destination_lifecycle_invariant (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (abandonTree id state).finalState := by
  simp only [abandonTree, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some parent =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact valid
      | true =>
          simp only [allowed]
          cases progress : parent.progress <;> try simp only [progress] <;> try exact valid
          all_goals
            simp only [pure, bind, ConstructionM.get]
            apply lifecycle_bind _ _ _ _ state valid
            · intro initial initialValid
              apply invariant_forIn
              · intro destination token before beforeValid
                cases destination with
                | mk capability backing layout use progress writeEnd rollbackEnd known adaptation =>
                    cases progress <;> exact beforeValid
              · exact initialValid
            · intro token after afterValid
              apply lifecycle_bind _ _ _ _ after afterValid
              · intro initial initialValid
                apply invariant_forIn
                · intro destination token before beforeValid
                  have expected := treeForInStep_preserves destination token before beforeValid
                  try simp only [treeForInStep, writableStep, writableDestination_result, bind] at expected ⊢
                  cases present : before.destinations[destination.capability.id]? with
                  | none => simpa only [present] using expected
                  | some current =>
                      cases allowed : destinationCanWrite before destination.capability.id with
                      | false => simpa only [present, allowed] using expected
                      | true =>
                          simp only [present, allowed] at expected ⊢
                          cases current with
                          | mk capability backing layout use progress writeEnd rollbackEnd known adaptation =>
                              cases progress <;> simpa only [replaceStep, bind, pure] using expected
                · exact initialValid
              · intro result tail tailValid
                exact tailValid

end Goose.Proofs.ConstructionExecutionProtocol
