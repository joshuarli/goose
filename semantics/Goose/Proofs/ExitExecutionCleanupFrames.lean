import Goose.Proofs.ExitExecutionBase

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Core

private abbrev KeepsConstructionStdout (action : ConstructionM α) : Prop :=
  ∀ state, (action state).finalState.stdout = state.stdout

private def cleanupFrameValue (state : ExecutionState) :=
  (state.objects, state.construction.stdout)

private abbrev KeepsCleanupFrame (action : EvalM α) : Prop :=
  ∀ state, cleanupFrameValue (Goose.Proofs.Exit.stepState (action state)) = cleanupFrameValue state

private theorem runtime_lift_keepsCleanupFrame (origin : OriginId) (action : ConstructionM α)
    (stdoutFrame : ∀ state, (action state).finalState.stdout = state.stdout) (state : ExecutionState) :
    cleanupFrameValue (Goose.Proofs.Exit.stepState (liftConstruction origin action state)) = cleanupFrameValue state := by
  apply Prod.ext
  · exact Goose.Proofs.Exit.runtime_lift_frames_objects origin action state
  · exact Goose.Proofs.Exit.runtime_lift_frames_output origin action stdoutFrame state

private theorem runtime_pure_keepsCleanupFrame (value : α) :
    KeepsCleanupFrame (pure value) := fun _ => rfl

private theorem runtime_bind_keepsCleanupFrame (action : EvalM α) (next : α → EvalM β)
    (first : KeepsCleanupFrame action) (remaining : ∀ value, KeepsCleanupFrame (next value)) :
    KeepsCleanupFrame (action >>= next) := by
  intro state
  exact Goose.Proofs.Exit.runtime_bind_frames cleanupFrameValue action next first remaining state

private theorem runtime_mapM_keepsCleanupFrame (items : List α) (action : α → EvalM β)
    (safe : ∀ item, KeepsCleanupFrame (action item)) :
    KeepsCleanupFrame (items.mapM action) := by
  induction items with
  | nil => exact fun _ => rfl
  | cons item rest ih =>
      intro state
      rw [List.mapM_cons]
      apply Goose.Proofs.Exit.runtime_bind_frames cleanupFrameValue (action item)
      · exact safe item
      · intro value after
        apply Goose.Proofs.Exit.runtime_bind_frames cleanupFrameValue (rest.mapM action)
        · exact ih
        · intro values final
          rfl

private theorem runtime_forInLoop_keepsCleanupFrame (values : List α)
    (body : (value : α) → value ∈ values → β → EvalM (ForInStep β))
    (safe : ∀ value member accumulator, KeepsCleanupFrame (body value member accumulator))
    (remaining : List α) (accumulator : β) (inside : ∃ earlier, earlier ++ remaining = values) :
    KeepsCleanupFrame (List.forIn'.loop values body remaining accumulator inside) := by
  induction remaining generalizing accumulator with
  | nil => exact fun _ => rfl
  | cons value rest ih =>
      simp only [List.forIn'.loop]
      apply runtime_bind_keepsCleanupFrame
      · intro state
        exact safe _ _ _ state
      · intro step
        cases step with
        | done accumulator => exact runtime_pure_keepsCleanupFrame accumulator
        | yield accumulator => exact ih _ _

private theorem runtime_forIn_keepsCleanupFrame (values : List α) (accumulator : β)
    (body : α → β → EvalM (ForInStep β))
    (safe : ∀ value accumulator, KeepsCleanupFrame (body value accumulator)) :
    KeepsCleanupFrame (forIn values accumulator body) := by
  apply runtime_forInLoop_keepsCleanupFrame
  intro value member current
  exact safe value current

private theorem runtime_foreach_keepsCleanupFrame (values : List α) (body : α → EvalM Unit)
    (safe : ∀ value, KeepsCleanupFrame (body value)) :
    KeepsCleanupFrame (do for value in values do body value) := by
  apply runtime_bind_keepsCleanupFrame
  · apply runtime_forIn_keepsCleanupFrame
    intro value member accumulator
    apply runtime_bind_keepsCleanupFrame (body value)
    · exact safe value
    · intro _
      exact runtime_pure_keepsCleanupFrame _
  · intro _
    exact runtime_pure_keepsCleanupFrame _

private theorem keepsConstructionStdout_bind (action : ConstructionM α) (next : α → ConstructionM β)
    (first : KeepsConstructionStdout action) (remaining : ∀ value, KeepsConstructionStdout (next value)) :
    KeepsConstructionStdout (action >>= next) := by
  intro state
  have framed := first state
  cases result : action state with
  | ok value after =>
      simp only [bind, result]
      exact (remaining value after).trans (by simpa [result, ConstructionResult.finalState] using framed)
  | fault reason after => simpa [bind, result, ConstructionResult.finalState] using framed

private theorem keepsConstructionStdout_getBind (next : ConstructionState → ConstructionM α)
    (safe : ∀ state, (next state state).finalState.stdout = state.stdout) :
    KeepsConstructionStdout (ConstructionM.get >>= next) := by
  intro state
  simp only [ConstructionM.get, bind]
  exact safe state

private theorem keepsConstructionStdout_pure (value : α) :
    KeepsConstructionStdout (pure value) := fun _ => rfl

private theorem keepsConstructionStdout_fail (reason : ConstructionFault) :
    KeepsConstructionStdout (ConstructionM.fail (α := α) reason) := fun _ => rfl

private theorem keepsConstructionStdout_fail_bind (reason : ConstructionFault) (next : α → ConstructionM β) :
    KeepsConstructionStdout (ConstructionM.fail reason >>= next) := fun _ => rfl

private theorem keepsConstructionStdout_get : KeepsConstructionStdout ConstructionM.get := fun _ => rfl

private abbrev frameEmit (event : ConstructionEvent) : ConstructionM Unit :=
  fun state => .ok () { state with events := state.events ++ [event] }

private theorem keepsConstructionStdout_emit (event : ConstructionEvent) :
    KeepsConstructionStdout (frameEmit event) := by
  intro state
  dsimp only [frameEmit]
  rfl

private theorem keepsConstructionStdout_if (condition : Prop) [Decidable condition]
    (yes no : ConstructionM α) (first : KeepsConstructionStdout yes)
    (second : KeepsConstructionStdout no) : KeepsConstructionStdout (if condition then yes else no) := by
  by_cases selected : condition
  · simpa only [selected, ↓reduceIte] using first
  · simpa only [selected, ↓reduceIte] using second

private theorem keepsConstructionStdout_forInLoop (values : List α)
    (body : (value : α) → value ∈ values → β → ConstructionM (ForInStep β))
    (safe : ∀ value member accumulator, KeepsConstructionStdout (body value member accumulator))
    (remaining : List α) (accumulator : β) (inside : ∃ earlier, earlier ++ remaining = values) :
    KeepsConstructionStdout (List.forIn'.loop values body remaining accumulator inside) := by
  induction remaining generalizing accumulator with
  | nil => exact keepsConstructionStdout_pure _
  | cons value rest ih =>
      simp only [List.forIn'.loop]
      apply keepsConstructionStdout_bind
      · exact safe _ _ _
      · intro step
        cases step with
        | done accumulator => exact keepsConstructionStdout_pure _
        | yield accumulator => exact ih _ _

private theorem keepsConstructionStdout_forIn (values : List α) (accumulator : β)
    (body : α → β → ConstructionM (ForInStep β))
    (safe : ∀ value accumulator, KeepsConstructionStdout (body value accumulator)) :
    KeepsConstructionStdout (forIn values accumulator body) := by
  apply keepsConstructionStdout_forInLoop
  intro value member current
  exact safe value current

private theorem keepsConstructionStdout_foreach (values : List α)
    (body : α → ConstructionM Unit) (safe : ∀ value, KeepsConstructionStdout (body value)) :
    KeepsConstructionStdout (do for value in values do body value) := by
  apply keepsConstructionStdout_bind
  · apply keepsConstructionStdout_forInLoop
    intro value member current
    apply keepsConstructionStdout_bind (body value)
    · exact safe value
    · intro _; exact keepsConstructionStdout_pure _
  · intro _; exact keepsConstructionStdout_pure _

private theorem keepsConstructionStdout_abandonDestination (id : DestinationId) :
    KeepsConstructionStdout (abandonDestination id) := by
  unfold abandonDestination
  apply keepsConstructionStdout_bind
  · intro state
    rw [writableDestination_result]
    cases state.destinations[id]? with
    | none => rfl
    | some destination => cases destinationCanWrite state id <;> rfl
  · intro destination
    cases destination.progress with
    | «open» _ | built _ =>
        apply keepsConstructionStdout_bind
        · intro state
          rw [lookupStorage_result]
          cases state.storage[destination.storage]? <;> rfl
        · intro storage
          apply keepsConstructionStdout_bind
          · intro state
            rw [replaceStorage_result]
            split <;> rfl
          · intro _
            apply keepsConstructionStdout_bind
            · intro state
              rw [replaceDestination_result]
              split <;> rfl
            · intro _
              simpa only [KeepsConstructionStdout, emit_result] using
                keepsConstructionStdout_emit (.abandon id)
    | suspended _ _ | exiting _ _ | published _ | attached _ | abandoned | cancelled | retired =>
        exact keepsConstructionStdout_fail .protocol

private theorem keepsConstructionStdout_abandonTree (id : DestinationId) :
    KeepsConstructionStdout (abandonTree id) := by
  unfold abandonTree
  apply keepsConstructionStdout_bind
  · intro state
    rw [writableDestination_result]
    cases state.destinations[id]? with
    | none => rfl
    | some destination => cases destinationCanWrite state id <;> rfl
  · intro parent
    cases parent.progress with
    | «open» _ | built _ | suspended _ _ =>
        apply keepsConstructionStdout_bind ConstructionM.get
        · exact keepsConstructionStdout_get
        · intro state
          apply keepsConstructionStdout_bind
          · apply keepsConstructionStdout_forIn
            intro destination accumulator
            cases destination.progress with
            | exiting _ _ => exact keepsConstructionStdout_fail_bind .protocol _
            | _ => exact keepsConstructionStdout_pure (ForInStep.yield accumulator)
          · intro _
            apply keepsConstructionStdout_bind
            · apply keepsConstructionStdout_forIn
              intro destination accumulator
              apply keepsConstructionStdout_bind
              · intro currentState
                rw [writableDestination_result]
                cases currentState.destinations[destination.capability.id]? with
                | none => rfl
                | some current => cases destinationCanWrite currentState destination.capability.id <;> rfl
              · intro current
                cases current.progress with
                | suspended count _ =>
                    apply keepsConstructionStdout_bind
                    · intro currentState
                      rw [replaceDestination_result]
                      split <;> rfl
                    · intro _
                      apply keepsConstructionStdout_bind (abandonDestination destination.capability.id)
                      · exact keepsConstructionStdout_abandonDestination destination.capability.id
                      · intro _
                        exact keepsConstructionStdout_pure (ForInStep.yield accumulator)
                | _ =>
                    apply keepsConstructionStdout_bind (abandonDestination destination.capability.id)
                    · exact keepsConstructionStdout_abandonDestination destination.capability.id
                    · intro _
                      exact keepsConstructionStdout_pure (ForInStep.yield accumulator)
            · intro _
              exact keepsConstructionStdout_pure ()
    | exiting _ _ | published _ | attached _ | abandoned | cancelled | retired =>
        exact keepsConstructionStdout_fail .protocol

theorem abandonTree_stdout (id : DestinationId) (state : ConstructionState) :
    (abandonTree id state).finalState.stdout = state.stdout :=
  keepsConstructionStdout_abandonTree id state


theorem releaseExitReservation_stdout (token : ExitReservationId) :
    ∀ state, (releaseExitReservation token state).finalState.stdout = state.stdout := by
  intro state
  unfold releaseExitReservation
  simp only [ConstructionM.get, bind]
  cases present : state.exitReservations[token]? with
  | none => simp [present, ConstructionM.fail, ConstructionResult.finalState, bind, pure]
  | some reservation => cases reservation <;>
      simp [present, ConstructionM.set, ConstructionM.fail, ConstructionResult.finalState, bind, pure]

theorem rearmExitReservation_stdout (borrowed : BorrowedWaitingExitReservation) :
    ∀ state, (rearmExitReservation borrowed state).finalState.stdout = state.stdout := by
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

theorem cancelExitReservation_stdout (token : ExitReservationId) (carried : List DestinationId) :
    ∀ state, (cancelExitReservation token carried state).finalState.stdout = state.stdout := by
  change KeepsConstructionStdout (cancelExitReservation token carried)
  unfold cancelExitReservation
  apply keepsConstructionStdout_getBind
  intro state
  cases present : state.exitReservations[token]? with
  | none => simp [present, ConstructionM.fail, bind, pure, ConstructionResult.finalState]
  | some reservation =>
      cases reservation with
      | restored | waiting _ => exact keepsConstructionStdout_pure () state
      | released => exact keepsConstructionStdout_fail .protocol state
      | active role incoming reserved snapshot =>
          cases role with
          | named stage => simp [ConstructionM.set, ConstructionResult.finalState]
          | fresh =>
              cases current : destinationCurrent state reserved with
              | error kind => simp [current, ConstructionM.fail, bind, pure, ConstructionResult.finalState]
              | ok selected =>
                  simp only [current, bind, pure]
                  split
                  · simp [bind, pure, ConstructionResult.finalState]
                  ·
                    cases present : state.destinations[selected]? with
                    | none => simp [lookupDestination_result, present, ConstructionResult.finalState]
                    | some destination =>
                        simp only [lookupDestination_result, present, bind]
                        split
                        · cases abandoned : abandonTree selected state with
                          | ok value after =>
                              have abandonedFrame := keepsConstructionStdout_abandonTree selected state
                              calc
                                _ = after.stdout := by
                                  simp only [abandoned, bind]
                                  by_cases replacement : (reserved != snapshot.capability.id) = true
                                  · simp only [replacement, ↓reduceIte, bind, ConstructionM.get, ConstructionM.set]
                                    cases found : after.destinations[snapshot.capability.id]? with
                                    | none => simp [lookupDestination_result, found, bind, ConstructionResult.finalState]
                                    | some superseded =>
                                        cases progress : superseded.progress <;>
                                          simp only [lookupDestination_result, found, progress, bind, ConstructionM.fail,
                                            ConstructionM.get, ConstructionM.set, pure, ConstructionResult.finalState]
                                        case exiting count expected =>
                                          by_cases mismatch : (expected != selected) = true
                                          · simp [mismatch, bind, ConstructionM.fail, ConstructionResult.finalState]
                                          · simp only [mismatch, Bool.false_eq_true, ↓reduceIte, replaceDestination_result]
                                            by_cases bounded : snapshot.capability.id < after.destinations.size <;>
                                              simp [bounded, ConstructionResult.finalState]
                                  · simp [replacement, bind, ConstructionM.get, ConstructionM.set, ConstructionResult.finalState]
                                _ = state.stdout := by
                                  simpa [abandoned, ConstructionResult.finalState] using abandonedFrame
                          | fault kind after =>
                              simpa only [abandoned, bind, ConstructionResult.finalState] using
                                keepsConstructionStdout_abandonTree selected state
                        ·
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

private theorem keepsConstructionStdout_restoreNamedDestination (id : DestinationId) :
    KeepsConstructionStdout (restoreNamedDestination id) := by
  unfold restoreNamedDestination
  apply keepsConstructionStdout_getBind
  intro state
  apply keepsConstructionStdout_foreach
  intro token
  exact cancelExitReservation_stdout token []

theorem materializeNamedReservation_stdout (token : ExitReservationId) :
    ∀ state, (materializeNamedReservation token state).finalState.stdout = state.stdout := by
  change KeepsConstructionStdout (materializeNamedReservation token)
  unfold materializeNamedReservation
  apply keepsConstructionStdout_getBind
  intro state
  cases ticket : state.exitReservations[token]? with
  | none => simp [ticket, ConstructionM.fail, ConstructionResult.finalState, bind, pure]
  | some reservation =>
      cases reservation with
      | waiting _ | restored | released =>
          simp [ticket, ConstructionM.fail, ConstructionResult.finalState, bind, pure]
      | active role incoming selected snapshot =>
          cases role with
          | fresh => simp [ticket, ConstructionM.fail, ConstructionResult.finalState, bind, pure]
          | named stage =>
              cases stage with
              | awaitingSource | materialized =>
                  simp [ticket, ConstructionM.fail, ConstructionResult.finalState, bind, pure]
              | ready =>
                  simp only [ticket, bind, pure]
                  apply keepsConstructionStdout_bind (restoreNamedDestination selected)
                  · exact keepsConstructionStdout_restoreNamedDestination selected
                  · intro _
                    apply keepsConstructionStdout_bind
                    · intro currentState
                      rw [lookupDestination_result]
                      cases currentState.destinations[selected]? <;> rfl
                    · intro parent
                      dsimp
                      apply keepsConstructionStdout_if
                      · exact keepsConstructionStdout_fail .ownership
                      · cases snapshot.progress with
                        | built originalCount =>
                          cases parent.progress with
                          | built count =>
                            apply keepsConstructionStdout_if
                            · exact keepsConstructionStdout_fail .ownership
                            · apply keepsConstructionStdout_bind
                              · intro state
                                rw [lookupStorage_result]
                                cases state.storage[snapshot.storage]? <;> rfl
                              · intro storage
                                apply keepsConstructionStdout_if
                                · exact keepsConstructionStdout_fail .ownership
                                · apply keepsConstructionStdout_bind
                                  · intro state
                                    rw [replaceDestination_result]
                                    split <;> rfl
                                  · intro _ state
                                    rfl
                          | suspended count expected =>
                            apply keepsConstructionStdout_if
                            · exact keepsConstructionStdout_fail .ownership
                            · apply keepsConstructionStdout_bind ConstructionM.get
                              · exact keepsConstructionStdout_get
                              · intro currentState
                                cases resolved : destinationCurrent currentState expected with
                                | error kind =>
                                  simp only [resolved, bind, ConstructionM.fail]
                                  exact keepsConstructionStdout_fail kind
                                | ok current =>
                                  simp only [resolved, bind, pure]
                                  apply keepsConstructionStdout_bind
                                  · intro state
                                    rw [lookupDestination_result]
                                    cases state.destinations[current]? <;> rfl
                                  · intro child
                                    apply keepsConstructionStdout_if
                                    · exact keepsConstructionStdout_fail .ownership
                                    · apply keepsConstructionStdout_bind
                                      · intro state
                                        rw [lookupStorage_result]
                                        cases state.storage[parent.storage]? <;> rfl
                                      · intro storage
                                        apply keepsConstructionStdout_if
                                        · exact keepsConstructionStdout_fail .ownership
                                        · cases child.backing with
                                          | direct backing =>
                                            apply keepsConstructionStdout_if
                                            · exact keepsConstructionStdout_fail .ownership
                                            · apply keepsConstructionStdout_if
                                              · apply keepsConstructionStdout_bind (abandonTree current)
                                                · exact keepsConstructionStdout_abandonTree current
                                                · intro _
                                                  apply keepsConstructionStdout_bind
                                                  · intro state
                                                    rw [lookupStorage_result]
                                                    cases state.storage[snapshot.storage]? <;> rfl
                                                  · intro storage
                                                    apply keepsConstructionStdout_if
                                                    · exact keepsConstructionStdout_fail .ownership
                                                    · apply keepsConstructionStdout_bind
                                                      · intro state
                                                        rw [replaceDestination_result]
                                                        split <;> rfl
                                                      · intro _
                                                        intro state
                                                        rfl
                                              · apply keepsConstructionStdout_bind
                                                · intro state
                                                  rw [lookupStorage_result]
                                                  cases state.storage[snapshot.storage]? <;> rfl
                                                · intro storage
                                                  apply keepsConstructionStdout_if
                                                  · exact keepsConstructionStdout_fail .ownership
                                                  · apply keepsConstructionStdout_bind
                                                    · intro state
                                                      rw [replaceDestination_result]
                                                      split <;> rfl
                                                    · intro _ state
                                                      rfl
                                          | staged receiver backing =>
                                            apply keepsConstructionStdout_if
                                            · apply keepsConstructionStdout_bind (abandonTree current)
                                              · exact keepsConstructionStdout_abandonTree current
                                              · intro _
                                                apply keepsConstructionStdout_bind
                                                · intro state
                                                  rw [lookupStorage_result]
                                                  cases state.storage[snapshot.storage]? <;> rfl
                                                · intro storage
                                                  apply keepsConstructionStdout_if
                                                  · exact keepsConstructionStdout_fail .ownership
                                                  · apply keepsConstructionStdout_bind
                                                    · intro state
                                                      rw [replaceDestination_result]
                                                      split <;> rfl
                                                    · intro _
                                                      intro state
                                                      rfl
                                            · apply keepsConstructionStdout_bind
                                              · intro state
                                                rw [lookupStorage_result]
                                                cases state.storage[snapshot.storage]? <;> rfl
                                              · intro storage
                                                apply keepsConstructionStdout_if
                                                · exact keepsConstructionStdout_fail .ownership
                                                · apply keepsConstructionStdout_bind
                                                  · intro state
                                                    rw [replaceDestination_result]
                                                    split <;> rfl
                                                  · intro _ state
                                                    rfl
                          | _ => exact keepsConstructionStdout_fail .protocol
                        | _ => exact keepsConstructionStdout_fail .protocol

private theorem materializeOwnedCarriers_cleanupFrame (origin : OriginId)
    (tokens : List ExitReservationId) (carriers : List Goose.Construct.Carrier) :
    KeepsCleanupFrame (materializeOwnedCarriers origin tokens carriers) := by
  unfold materializeOwnedCarriers
  apply runtime_mapM_keepsCleanupFrame
  intro carrier
  cases carrier with
  | register value => exact fun _ => rfl
  | completed destination => exact fun _ => rfl
  | pendingNamed token =>
      cases owned : tokens.contains token with
      | false => simp only [owned, ↓reduceIte]; exact fun _ => rfl
      | true =>
          simp only [owned, ↓reduceIte]
          apply runtime_bind_keepsCleanupFrame
          · intro state
            exact runtime_lift_keepsCleanupFrame origin (materializeNamedReservation token)
              (materializeNamedReservation_stdout token) state
          · intro destination
            exact runtime_pure_keepsCleanupFrame _

theorem materializeOwnedCarriers_stdout (origin : OriginId) (tokens : List ExitReservationId)
    (carriers : List Goose.Construct.Carrier) :
    ∀ state, (Goose.Proofs.Exit.stepState (materializeOwnedCarriers origin tokens carriers state)).construction.stdout =
      state.construction.stdout := by
  intro state
  exact congrArg Prod.snd (materializeOwnedCarriers_cleanupFrame origin tokens carriers state)

theorem materializeOwnedCarriers_objects (origin : OriginId) (tokens : List ExitReservationId)
    (carriers : List Goose.Construct.Carrier) :
    ∀ state, (Goose.Proofs.Exit.stepState (materializeOwnedCarriers origin tokens carriers state)).objects =
      state.objects := by
  intro state
  exact congrArg Prod.fst (materializeOwnedCarriers_cleanupFrame origin tokens carriers state)

private theorem borrowedExitChannelStep_cleanupFrame (origin : OriginId) (carriers : List Goose.Construct.Carrier)
    (receipt : BorrowedWaitingExitReservation) :
    KeepsCleanupFrame (borrowedExitChannelStep origin carriers receipt) := by
  unfold borrowedExitChannelStep
  dsimp only
  split <;> first | (intro state; rfl) | skip
  apply runtime_bind_keepsCleanupFrame
  · intro state
    exact runtime_lift_keepsCleanupFrame origin
      (cancelExitReservation receipt.token (carriers.filterMap fun carrier =>
        match carrier with | .completed id => some id | _ => none))
      (cancelExitReservation_stdout receipt.token _) state
  · intro _ after
    apply runtime_bind_keepsCleanupFrame
    · intro state
      rfl
    · intro state current
      cases present : state.construction.exitReservations[receipt.token]? with
      | none =>
          simp [present, bind, Goose.Construct.fault, EvalM.stop]
          rfl
      | some reservation =>
          cases reservation with
          | restored =>
              simp only [present]
              apply runtime_bind_keepsCleanupFrame
              · intro currentState
                exact runtime_lift_keepsCleanupFrame origin (rearmExitReservation receipt)
                  (rearmExitReservation_stdout receipt) currentState
              · intro _ finalState
                rfl
          | released =>
              simp [present, bind, Goose.Construct.fault, EvalM.stop]
              rfl
          | active role incoming selected snapshot =>
              simp [present, bind, pure]
              rfl
          | waiting incoming =>
              cases mismatch : incoming != receipt.incoming with
              | false =>
                  simp [present, mismatch, bind, pure]
                  rfl
              | true =>
                  simp [present, mismatch, bind, Goose.Construct.fault, EvalM.stop]
                  rfl


private theorem exitChannelCleanupToken_cleanupFrame (origin : OriginId)
    (cancel : Bool) (carriers : List Goose.Construct.Carrier)
    (token : ExitReservationId) :
    KeepsCleanupFrame (do
      if cancel then
        liftConstruction origin (cancelExitReservation token (carriers.filterMap fun carrier =>
          match carrier with | .completed id => some id | _ => none))
      liftConstruction origin (releaseExitReservation token)) := by
  cases cancel with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      intro state
      exact runtime_lift_keepsCleanupFrame origin (releaseExitReservation token)
        (releaseExitReservation_stdout token) state
  | true =>
      simp only [↓reduceIte]
      apply runtime_bind_keepsCleanupFrame
      · intro state
        exact runtime_lift_keepsCleanupFrame origin
          (cancelExitReservation token (carriers.filterMap fun carrier =>
            match carrier with | .completed id => some id | _ => none))
          (cancelExitReservation_stdout token _) state
      · intro _ after
        exact runtime_lift_keepsCleanupFrame origin (releaseExitReservation token)
          (releaseExitReservation_stdout token) after

private theorem exitChannelCleanupBorrowed_cleanupFrame (origin : OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Goose.Construct.Carrier) :
    KeepsCleanupFrame (exitChannelCleanupBorrowed origin borrowed tokens cancel carriers) := by
  unfold exitChannelCleanupBorrowed
  cases cancel with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply runtime_foreach_keepsCleanupFrame
      intro token
      exact exitChannelCleanupToken_cleanupFrame origin false carriers token
  | true =>
      simp only [↓reduceIte]
      apply runtime_bind_keepsCleanupFrame
      · apply runtime_forIn_keepsCleanupFrame
        intro receipt current
        exact borrowedExitChannelStep_cleanupFrame origin carriers receipt
      · intro _ after
        apply runtime_bind_keepsCleanupFrame
        · apply runtime_forIn_keepsCleanupFrame
          intro token member current
          apply runtime_bind_keepsCleanupFrame
          · intro state
            exact runtime_lift_keepsCleanupFrame origin
              (cancelExitReservation token (carriers.filterMap fun carrier =>
                match carrier with | .completed id => some id | _ => none))
              (cancelExitReservation_stdout token _) state
          · intro _ after
            apply runtime_bind_keepsCleanupFrame
            · intro state
              exact runtime_lift_keepsCleanupFrame origin (releaseExitReservation token)
                (releaseExitReservation_stdout token) state
            · intro _
              exact runtime_pure_keepsCleanupFrame (ForInStep.yield current)
        · intro _
          exact runtime_pure_keepsCleanupFrame ()

theorem exitChannelCleanupBorrowed_stdout (origin : OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Goose.Construct.Carrier) :
    ∀ state,
      (Goose.Proofs.Exit.stepState
        (exitChannelCleanupBorrowed origin borrowed tokens cancel carriers state)).construction.stdout =
        state.construction.stdout := by
  intro state
  exact congrArg Prod.snd (exitChannelCleanupBorrowed_cleanupFrame origin borrowed tokens cancel carriers state)

theorem exitChannelCleanupBorrowed_objects (origin : OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Goose.Construct.Carrier) :
    ∀ state,
      (Goose.Proofs.Exit.stepState
        (exitChannelCleanupBorrowed origin borrowed tokens cancel carriers state)).objects =
        state.objects := by
  intro state
  exact congrArg Prod.fst (exitChannelCleanupBorrowed_cleanupFrame origin borrowed tokens cancel carriers state)
