import Goose.Proofs.ExitExecutionCleanupFrames
import Init.Data.ByteArray.Lemmas

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core

structure CleanupStorageBoundary where
  storage : StorageId
  retainedEnd : Nat

inductive CleanupStorageTrace : List CleanupStorageBoundary →
    Array ReceivingStorage → Array ReceivingStorage → Prop
  | refl (storage : Array ReceivingStorage) : CleanupStorageTrace [] storage storage
  | cut (storage : Array ReceivingStorage) (id : StorageId)
      (previous : ReceivingStorage) (finish : Nat)
      (present : storage[id]? = some previous) :
      CleanupStorageTrace [⟨id, finish⟩] storage
        (storage.set! id { previous with bytes := previous.bytes.extract 0 finish })
  | rewrite (storage : Array ReceivingStorage) (id : StorageId)
      (previous current : ReceivingStorage) (finish : Nat)
      (present : storage[id]? = some previous)
      (count : current.publishedCount = previous.publishedCount)
      (bytes : current.bytes.extract 0 finish = previous.bytes.extract 0 finish) :
      CleanupStorageTrace [⟨id, finish⟩] storage (storage.set! id current)
  | append {first second : List CleanupStorageBoundary} {before middle after : Array ReceivingStorage}
      (left : CleanupStorageTrace first before middle)
      (right : CleanupStorageTrace second middle after) :
      CleanupStorageTrace (first ++ second) before after

def ConstructionCleanupStorage (action : ConstructionM α) : Prop :=
  ∀ state, ∃ cuts, CleanupStorageTrace cuts state.storage (action state).finalState.storage

theorem ConstructionCleanupStorage.of_storage_eq (action : ConstructionM α)
    (frame : ∀ state, (action state).finalState.storage = state.storage) :
    ConstructionCleanupStorage action := by
  intro state
  rw [frame]
  exact ⟨[], .refl _⟩

theorem ConstructionCleanupStorage.bind (action : ConstructionM α) (next : α → ConstructionM β)
    (first : ConstructionCleanupStorage action)
    (remaining : ∀ value, ConstructionCleanupStorage (next value)) :
    ConstructionCleanupStorage (action >>= next) := by
  intro state
  obtain ⟨cuts, framed⟩ := first state
  cases result : action state with
  | fault reason after =>
      exact ⟨cuts, by simpa only [Bind.bind, ConstructionM.instMonad, result, ConstructionResult.finalState] using framed⟩
  | ok value after =>
      obtain ⟨later, framedLater⟩ := remaining value after
      exact ⟨cuts ++ later, .append
        (by simpa only [result, ConstructionResult.finalState] using framed)
        (by simpa only [Bind.bind, ConstructionM.instMonad, result] using framedLater)⟩

theorem ConstructionCleanupStorage.bind_at (action : ConstructionM α) (next : α → ConstructionM β)
    (state : ConstructionState)
    (first : ∃ cuts, CleanupStorageTrace cuts state.storage (action state).finalState.storage)
    (remaining : ∀ value, ConstructionCleanupStorage (next value)) :
    ∃ cuts, CleanupStorageTrace cuts state.storage ((action >>= next) state).finalState.storage := by
  obtain ⟨cuts, framed⟩ := first
  cases result : action state with
  | fault reason after =>
      exact ⟨cuts, by simpa only [Bind.bind, ConstructionM.instMonad, result,
        ConstructionResult.finalState] using framed⟩
  | ok value after =>
      obtain ⟨later, framedLater⟩ := remaining value after
      exact ⟨cuts ++ later, .append
        (by simpa only [result, ConstructionResult.finalState] using framed)
        (by simpa only [Bind.bind, ConstructionM.instMonad, result] using framedLater)⟩

theorem ConstructionCleanupStorage.query_bind (action : ConstructionM α) (next : α → ConstructionM β)
    (query : ∀ state, (action state).finalState = state)
    (remaining : ∀ state value, action state = .ok value state →
      ∃ cuts, CleanupStorageTrace cuts state.storage (next value state).finalState.storage) :
    ConstructionCleanupStorage (action >>= next) := by
  intro state
  have current := query state
  cases result : action state with
  | fault reason after =>
      simp only [result, ConstructionResult.finalState] at current
      subst after
      simp only [Bind.bind, ConstructionM.instMonad, result, ConstructionResult.finalState]
      exact ⟨[], .refl _⟩
  | ok value after =>
      simp only [result, ConstructionResult.finalState] at current
      subst after
      simpa only [Bind.bind, ConstructionM.instMonad, result] using remaining state value result

theorem ConstructionCleanupStorage.ite_at (condition : Prop) [Decidable condition]
    (yes no : ConstructionM α) (state : ConstructionState)
    (first : condition → ∃ cuts, CleanupStorageTrace cuts state.storage (yes state).finalState.storage)
    (second : ¬ condition → ∃ cuts, CleanupStorageTrace cuts state.storage (no state).finalState.storage) :
    ∃ cuts, CleanupStorageTrace cuts state.storage
      ((if condition then yes else no) state).finalState.storage := by
  by_cases selected : condition
  · simpa only [selected, ↓reduceIte] using first selected
  · simpa only [selected, ↓reduceIte] using second selected

theorem ConstructionCleanupStorage.pure (value : α) : ConstructionCleanupStorage (pure value) :=
  .of_storage_eq _ (fun _ => rfl)

theorem ConstructionCleanupStorage.fail (reason : ConstructionFault) :
    ConstructionCleanupStorage (ConstructionM.fail (α := α) reason) :=
  .of_storage_eq _ (fun _ => rfl)

theorem ConstructionCleanupStorage.get : ConstructionCleanupStorage ConstructionM.get :=
  .of_storage_eq _ (fun _ => rfl)

theorem releaseExitReservation_storage (token : ExitReservationId) :
    ∀ state, (releaseExitReservation token state).finalState.storage = state.storage := by
  intro state
  unfold releaseExitReservation
  simp only [ConstructionM.get, bind]
  cases present : state.exitReservations[token]? with
  | none => simp [present, ConstructionM.fail, ConstructionResult.finalState, bind, pure]
  | some reservation => cases reservation <;>
      simp [present, ConstructionM.set, ConstructionM.fail, ConstructionResult.finalState, bind, pure]

theorem rearmExitReservation_storage (borrowed : BorrowedWaitingExitReservation) :
    ∀ state, (rearmExitReservation borrowed state).finalState.storage = state.storage := by
  intro state
  unfold rearmExitReservation
  simp only [ConstructionM.get, bind]
  cases ticket : state.exitReservations[borrowed.token]? with
  | none => rfl
  | some reservation =>
      cases reservation with
      | active role incoming selected snapshot => rfl
      | waiting incoming => rfl
      | released => rfl
      | restored =>
          cases current : destinationCurrent state borrowed.incoming with
          | error kind => simp [current, ConstructionM.fail, ConstructionResult.finalState]
          | ok selected =>
              simp only [current, pure, bind, lookupDestination_result]
              cases present : state.destinations[selected]? <;> rfl

theorem abandonDestination_storage (id : DestinationId) :
    ConstructionCleanupStorage (abandonDestination id) := by
  intro state
  unfold abandonDestination
  simp only [Bind.bind, writableDestination_result]
  cases found : state.destinations[id]? with
  | none => exact ⟨[], .refl _⟩
  | some destination =>
      cases writable : destinationCanWrite state id with
      | false => simp only [writable, Bool.false_eq_true, ↓reduceIte]; exact ⟨[], .refl _⟩
      | true =>
          simp only [writable, ↓reduceIte]
          cases progress : destination.progress <;>
            simp only [progress, bind, ConstructionM.fail, ConstructionResult.finalState]
          case «open» count | built count =>
            simp only [lookupStorage_result, bind]
            cases stored : state.storage[destination.storage]? with
            | none => simp only [stored, bind, ConstructionResult.finalState]; exact ⟨[], .refl _⟩
            | some storage =>
                simp only [stored, bind]
                simp only [replaceStorage_result, bind]
                by_cases bounded : destination.storage < state.storage.size
                · simp only [bounded, ↓reduceIte, replaceDestination_result, bind]
                  by_cases destinationBounded : id < state.destinations.size
                  · simp only [destinationBounded, ↓reduceIte, emit_result,
                      ConstructionResult.finalState]
                    exact ⟨[⟨destination.storage, destination.rollbackEnd⟩],
                      .cut _ _ _ _ stored⟩
                  · simp only [destinationBounded, ↓reduceIte, ConstructionResult.finalState]
                    exact ⟨[⟨destination.storage, destination.rollbackEnd⟩],
                      .cut _ _ _ _ stored⟩
                · simp only [bounded, ↓reduceIte, ConstructionResult.finalState]
                  exact ⟨[], .refl _⟩
          all_goals exact ⟨[], .refl _⟩

theorem ConstructionCleanupStorage.getBind (next : ConstructionState → ConstructionM α)
    (safe : ∀ state, ∃ cuts, CleanupStorageTrace cuts state.storage (next state state).finalState.storage) :
    ConstructionCleanupStorage (ConstructionM.get >>= next) := by
  intro state
  simpa only [ConstructionM.get, Bind.bind, ConstructionM.instMonad] using safe state

theorem ConstructionCleanupStorage.fail_bind (reason : ConstructionFault) (next : α → ConstructionM β) :
    ConstructionCleanupStorage (ConstructionM.fail reason >>= next) :=
  .of_storage_eq _ (fun _ => rfl)

theorem ConstructionCleanupStorage.ite (condition : Prop) [Decidable condition]
    (yes no : ConstructionM α) (first : ConstructionCleanupStorage yes)
    (second : ConstructionCleanupStorage no) :
    ConstructionCleanupStorage (if condition then yes else no) := by
  by_cases selected : condition
  · simpa only [selected, ↓reduceIte] using first
  · simpa only [selected, ↓reduceIte] using second

private theorem constructionStorage_forInLoop (values : List α)
    (body : (value : α) → value ∈ values → β → ConstructionM (ForInStep β))
    (safe : ∀ value member accumulator, ConstructionCleanupStorage (body value member accumulator))
    (remaining : List α) (accumulator : β) (inside : ∃ earlier, earlier ++ remaining = values) :
    ConstructionCleanupStorage (List.forIn'.loop values body remaining accumulator inside) := by
  induction remaining generalizing accumulator with
  | nil => exact .pure _
  | cons value rest ih =>
      simp only [List.forIn'.loop]
      apply ConstructionCleanupStorage.bind
      · exact safe _ _ _
      · intro step
        cases step with
        | done accumulator => exact .pure _
        | yield accumulator => exact ih _ _

theorem ConstructionCleanupStorage.forIn (values : List α) (accumulator : β)
    (body : α → β → ConstructionM (ForInStep β))
    (safe : ∀ value accumulator, ConstructionCleanupStorage (body value accumulator)) :
    ConstructionCleanupStorage (forIn values accumulator body) := by
  apply constructionStorage_forInLoop
  intro value member current
  exact safe value current

theorem ConstructionCleanupStorage.foreach (values : List α)
    (body : α → ConstructionM Unit) (safe : ∀ value, ConstructionCleanupStorage (body value)) :
    ConstructionCleanupStorage (do for value in values do body value) := by
  apply ConstructionCleanupStorage.bind
  · apply constructionStorage_forInLoop
    intro value member current
    apply ConstructionCleanupStorage.bind (body value)
    · exact safe value
    · intro _; exact .pure _
  · intro _; exact .pure _

theorem abandonTree_storage (id : DestinationId) :
    ConstructionCleanupStorage (abandonTree id) := by
  unfold abandonTree
  apply ConstructionCleanupStorage.bind
  · apply ConstructionCleanupStorage.of_storage_eq
    intro state
    rw [writableDestination_result]
    cases state.destinations[id]? with
    | none => rfl
    | some destination => cases destinationCanWrite state id <;> rfl
  · intro parent
    cases parent.progress with
    | «open» _ | built _ | suspended _ _ =>
        apply ConstructionCleanupStorage.bind ConstructionM.get
        · exact ConstructionCleanupStorage.get
        · intro state
          apply ConstructionCleanupStorage.bind
          · apply ConstructionCleanupStorage.forIn
            intro destination accumulator
            cases destination.progress with
            | exiting _ _ => exact ConstructionCleanupStorage.fail_bind .protocol _
            | _ => exact ConstructionCleanupStorage.pure (ForInStep.yield accumulator)
          · intro _
            apply ConstructionCleanupStorage.bind
            · apply ConstructionCleanupStorage.forIn
              intro destination accumulator
              apply ConstructionCleanupStorage.bind
              · apply ConstructionCleanupStorage.of_storage_eq
                intro currentState
                rw [writableDestination_result]
                cases currentState.destinations[destination.capability.id]? with
                | none => rfl
                | some current => cases destinationCanWrite currentState destination.capability.id <;> rfl
              · intro current
                cases current.progress with
                | suspended count _ =>
                    apply ConstructionCleanupStorage.bind
                    · apply ConstructionCleanupStorage.of_storage_eq
                      intro currentState
                      rw [replaceDestination_result]
                      split <;> rfl
                    · intro _
                      apply ConstructionCleanupStorage.bind (abandonDestination destination.capability.id)
                      · exact abandonDestination_storage destination.capability.id
                      · intro _
                        exact ConstructionCleanupStorage.pure (ForInStep.yield accumulator)
                | _ =>
                    apply ConstructionCleanupStorage.bind (abandonDestination destination.capability.id)
                    · exact abandonDestination_storage destination.capability.id
                    · intro _
                      exact ConstructionCleanupStorage.pure (ForInStep.yield accumulator)
            · intro _
              exact ConstructionCleanupStorage.pure ()
    | exiting _ _ | published _ | attached _ | abandoned | cancelled | retired =>
        exact ConstructionCleanupStorage.fail .protocol

theorem cancelExitReservation_storage (token : ExitReservationId) (carried : List DestinationId) :
    ConstructionCleanupStorage (cancelExitReservation token carried) := by
  unfold cancelExitReservation
  apply ConstructionCleanupStorage.getBind
  intro state
  cases present : state.exitReservations[token]? with
  | none => simp only [ConstructionM.fail, bind, pure]; exact ⟨[], .refl _⟩
  | some reservation =>
      cases reservation with
      | restored | waiting _ => exact ⟨[], .refl _⟩
      | released => exact ⟨[], .refl _⟩
      | active role incoming reserved snapshot =>
          cases role with
          | named stage => exact ⟨[], .refl _⟩
          | fresh =>
              cases current : destinationCurrent state reserved with
              | error kind => simp only [current, ConstructionM.fail, bind, pure]; exact ⟨[], .refl _⟩
              | ok selected =>
                  simp only [current, bind, pure]
                  split
                  · exact ⟨[], .refl _⟩
                  · apply ConstructionCleanupStorage.bind _ _ ?_ ?_ state
                    · apply ConstructionCleanupStorage.of_storage_eq
                      intro state
                      rw [lookupDestination_result]
                      cases state.destinations[selected]? <;> rfl
                    · intro destination
                      apply ConstructionCleanupStorage.ite
                      · apply ConstructionCleanupStorage.bind (abandonTree selected)
                        · exact abandonTree_storage selected
                        · intro _
                          apply ConstructionCleanupStorage.of_storage_eq
                          intro state
                          by_cases replacement : (reserved != snapshot.capability.id) = true
                          · simp only [replacement, ↓reduceIte, bind, ConstructionM.get, ConstructionM.set]
                            cases found : state.destinations[snapshot.capability.id]? with
                            | none => simp [lookupDestination_result, found, bind, ConstructionResult.finalState]
                            | some superseded =>
                                cases progress : superseded.progress <;>
                                  simp only [lookupDestination_result, found, progress, bind, ConstructionM.fail,
                                    ConstructionM.get, ConstructionM.set, pure, ConstructionResult.finalState]
                                case exiting count expected =>
                                  by_cases mismatch : (expected != selected) = true
                                  · simp [mismatch, bind, ConstructionM.fail, ConstructionResult.finalState]
                                  · simp only [mismatch, Bool.false_eq_true, ↓reduceIte, replaceDestination_result]
                                    by_cases bounded : snapshot.capability.id < state.destinations.size <;>
                                      simp [bounded, ConstructionResult.finalState]
                          · simp [replacement, bind, ConstructionM.get, ConstructionM.set, ConstructionResult.finalState]
                      · apply ConstructionCleanupStorage.of_storage_eq
                        intro state
                        by_cases replacement : (reserved != snapshot.capability.id) = true
                        · simp only [replacement, ↓reduceIte, bind, ConstructionM.get, ConstructionM.set]
                          cases found : state.destinations[snapshot.capability.id]? with
                          | none => simp [lookupDestination_result, found, bind, ConstructionResult.finalState]
                          | some superseded =>
                              cases progress : superseded.progress <;>
                                simp only [lookupDestination_result, found, progress, bind, ConstructionM.fail,
                                  ConstructionM.get, ConstructionM.set, pure, ConstructionResult.finalState]
                              case exiting count expected =>
                                by_cases mismatch : (expected != selected) = true
                                · simp [mismatch, bind, ConstructionM.fail, ConstructionResult.finalState]
                                · simp only [mismatch, Bool.false_eq_true, ↓reduceIte, replaceDestination_result]
                                  by_cases bounded : snapshot.capability.id < state.destinations.size <;>
                                    simp [bounded, ConstructionResult.finalState]
                        · simp [replacement, bind, ConstructionM.get, ConstructionM.set, ConstructionResult.finalState]

theorem restoreNamedDestination_storage (id : DestinationId) :
    ConstructionCleanupStorage (restoreNamedDestination id) := by
  unfold restoreNamedDestination
  apply ConstructionCleanupStorage.getBind
  intro state
  apply ConstructionCleanupStorage.foreach
  intro token
  exact cancelExitReservation_storage token []

theorem materializeNamedReservation_storage (token : ExitReservationId) :
    ConstructionCleanupStorage (materializeNamedReservation token) := by
  unfold materializeNamedReservation
  apply ConstructionCleanupStorage.getBind
  intro state
  cases ticket : state.exitReservations[token]? with
  | none => simp [ticket, ConstructionM.fail, ConstructionResult.finalState, bind, pure]; exact ⟨[], .refl _⟩
  | some reservation =>
      cases reservation with
      | waiting _ | restored | released =>
          simp [ticket, ConstructionM.fail, ConstructionResult.finalState, bind, pure]; exact ⟨[], .refl _⟩
      | active role incoming selected snapshot =>
          cases role with
          | fresh => simp [ticket, ConstructionM.fail, ConstructionResult.finalState, bind, pure]; exact ⟨[], .refl _⟩
          | named stage =>
              cases stage with
              | awaitingSource | materialized =>
                  simp [ticket, ConstructionM.fail, ConstructionResult.finalState, bind, pure]; exact ⟨[], .refl _⟩
              | ready =>
                  simp only [ticket, bind, pure]
                  apply ConstructionCleanupStorage.bind (restoreNamedDestination selected)
                  · exact restoreNamedDestination_storage selected
                  · intro _
                    apply ConstructionCleanupStorage.bind
                    · apply ConstructionCleanupStorage.of_storage_eq
                      intro currentState
                      rw [lookupDestination_result]
                      cases currentState.destinations[selected]? <;> rfl
                    · intro parent
                      dsimp
                      apply ConstructionCleanupStorage.ite
                      · exact ConstructionCleanupStorage.fail .ownership
                      · cases snapshot.progress with
                        | built originalCount =>
                          cases parent.progress with
                          | built count =>
                            apply ConstructionCleanupStorage.ite
                            · exact ConstructionCleanupStorage.fail .ownership
                            · apply ConstructionCleanupStorage.bind
                              · apply ConstructionCleanupStorage.of_storage_eq
                                intro state
                                rw [lookupStorage_result]
                                cases state.storage[snapshot.storage]? <;> rfl
                              · intro storage
                                apply ConstructionCleanupStorage.ite
                                · exact ConstructionCleanupStorage.fail .ownership
                                · apply ConstructionCleanupStorage.bind
                                  · apply ConstructionCleanupStorage.of_storage_eq
                                    intro state
                                    rw [replaceDestination_result]
                                    split <;> rfl
                                  · intro _
                                    exact .of_storage_eq _ (fun _ => rfl)
                          | suspended count expected =>
                            apply ConstructionCleanupStorage.ite
                            · exact ConstructionCleanupStorage.fail .ownership
                            · apply ConstructionCleanupStorage.bind ConstructionM.get
                              · exact ConstructionCleanupStorage.get
                              · intro currentState
                                cases resolved : destinationCurrent currentState expected with
                                | error kind =>
                                  simp only [resolved, bind, ConstructionM.fail]
                                  exact ConstructionCleanupStorage.fail kind
                                | ok current =>
                                  simp only [resolved, bind, pure]
                                  apply ConstructionCleanupStorage.bind
                                  · apply ConstructionCleanupStorage.of_storage_eq
                                    intro state
                                    rw [lookupDestination_result]
                                    cases state.destinations[current]? <;> rfl
                                  · intro child
                                    apply ConstructionCleanupStorage.ite
                                    · exact ConstructionCleanupStorage.fail .ownership
                                    · apply ConstructionCleanupStorage.bind
                                      · apply ConstructionCleanupStorage.of_storage_eq
                                        intro state
                                        rw [lookupStorage_result]
                                        cases state.storage[parent.storage]? <;> rfl
                                      · intro storage
                                        apply ConstructionCleanupStorage.ite
                                        · exact ConstructionCleanupStorage.fail .ownership
                                        · cases child.backing with
                                          | direct backing =>
                                            apply ConstructionCleanupStorage.ite
                                            · exact ConstructionCleanupStorage.fail .ownership
                                            · apply ConstructionCleanupStorage.ite
                                              · apply ConstructionCleanupStorage.bind (abandonTree current)
                                                · exact abandonTree_storage current
                                                · intro _
                                                  apply ConstructionCleanupStorage.bind
                                                  · apply ConstructionCleanupStorage.of_storage_eq
                                                    intro state
                                                    rw [lookupStorage_result]
                                                    cases state.storage[snapshot.storage]? <;> rfl
                                                  · intro storage
                                                    apply ConstructionCleanupStorage.ite
                                                    · exact ConstructionCleanupStorage.fail .ownership
                                                    · apply ConstructionCleanupStorage.bind
                                                      · apply ConstructionCleanupStorage.of_storage_eq
                                                        intro state
                                                        rw [replaceDestination_result]
                                                        split <;> rfl
                                                      · intro _
                                                        exact .of_storage_eq _ (fun _ => rfl)
                                              · apply ConstructionCleanupStorage.bind
                                                · apply ConstructionCleanupStorage.of_storage_eq
                                                  intro state
                                                  rw [lookupStorage_result]
                                                  cases state.storage[snapshot.storage]? <;> rfl
                                                · intro storage
                                                  apply ConstructionCleanupStorage.ite
                                                  · exact ConstructionCleanupStorage.fail .ownership
                                                  · apply ConstructionCleanupStorage.bind
                                                    · apply ConstructionCleanupStorage.of_storage_eq
                                                      intro state
                                                      rw [replaceDestination_result]
                                                      split <;> rfl
                                                    · intro _
                                                      exact .of_storage_eq _ (fun _ => rfl)
                                          | staged receiver backing =>
                                            apply ConstructionCleanupStorage.ite
                                            · apply ConstructionCleanupStorage.bind (abandonTree current)
                                              · exact abandonTree_storage current
                                              · intro _
                                                apply ConstructionCleanupStorage.bind
                                                · apply ConstructionCleanupStorage.of_storage_eq
                                                  intro state
                                                  rw [lookupStorage_result]
                                                  cases state.storage[snapshot.storage]? <;> rfl
                                                · intro storage
                                                  apply ConstructionCleanupStorage.ite
                                                  · exact ConstructionCleanupStorage.fail .ownership
                                                  · apply ConstructionCleanupStorage.bind
                                                    · apply ConstructionCleanupStorage.of_storage_eq
                                                      intro state
                                                      rw [replaceDestination_result]
                                                      split <;> rfl
                                                    · intro _
                                                      exact .of_storage_eq _ (fun _ => rfl)
                                            · apply ConstructionCleanupStorage.bind
                                              · apply ConstructionCleanupStorage.of_storage_eq
                                                intro state
                                                rw [lookupStorage_result]
                                                cases state.storage[snapshot.storage]? <;> rfl
                                              · intro storage
                                                apply ConstructionCleanupStorage.ite
                                                · exact ConstructionCleanupStorage.fail .ownership
                                                · apply ConstructionCleanupStorage.bind
                                                  · apply ConstructionCleanupStorage.of_storage_eq
                                                    intro state
                                                    rw [replaceDestination_result]
                                                    split <;> rfl
                                                  · intro _
                                                    exact .of_storage_eq _ (fun _ => rfl)
                          | _ => exact ConstructionCleanupStorage.fail .protocol
                        | _ => exact ConstructionCleanupStorage.fail .protocol

end Goose.Proofs.ExitExecution
