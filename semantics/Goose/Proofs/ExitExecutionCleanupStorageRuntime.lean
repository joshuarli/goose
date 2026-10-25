import Goose.Proofs.ExitExecutionCleanupStorage

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core

def RuntimeCleanupStorage (action : EvalM α) : Prop :=
  ∀ state, ∃ cuts, CleanupStorageTrace cuts state.construction.storage
    (Goose.Proofs.Exit.stepState (action state)).construction.storage

theorem RuntimeCleanupStorage.of_storage_eq (action : EvalM α)
    (frame : ∀ state,
      (Goose.Proofs.Exit.stepState (action state)).construction.storage = state.construction.storage) :
    RuntimeCleanupStorage action := by
  intro state
  rw [frame]
  exact ⟨[], .refl _⟩

theorem RuntimeCleanupStorage.lift (origin : OriginId) (action : ConstructionM α)
    (frame : ConstructionCleanupStorage action) : RuntimeCleanupStorage (liftConstruction origin action) := by
  intro state
  obtain ⟨cuts, framed⟩ := frame state.construction
  cases result : action state.construction <;>
    exact ⟨cuts, by simpa only [liftConstruction, result, Goose.Proofs.Exit.stepState,
      ConstructionResult.finalState] using framed⟩

theorem RuntimeCleanupStorage.pure (value : α) : RuntimeCleanupStorage (pure value) :=
  .of_storage_eq _ (fun _ => rfl)

theorem RuntimeCleanupStorage.bind (action : EvalM α) (next : α → EvalM β)
    (first : RuntimeCleanupStorage action) (remaining : ∀ value, RuntimeCleanupStorage (next value)) :
    RuntimeCleanupStorage (action >>= next) := by
  intro state
  obtain ⟨cuts, framed⟩ := first state
  cases result : action state with
  | ok value after =>
      obtain ⟨later, framedLater⟩ := remaining value after
      exact ⟨cuts ++ later, .append
        (by simpa only [result, Goose.Proofs.Exit.stepState] using framed)
        (by simpa only [Bind.bind, EvalM.instMonad, result] using framedLater)⟩
  | stop reason after | jump target kind after | escape address carriers after =>
      exact ⟨cuts, by simpa only [Bind.bind, EvalM.instMonad, result,
        Goose.Proofs.Exit.stepState] using framed⟩

theorem RuntimeCleanupStorage.mapM (items : List α) (action : α → EvalM β)
    (safe : ∀ item, RuntimeCleanupStorage (action item)) :
    RuntimeCleanupStorage (items.mapM action) := by
  induction items with
  | nil => exact .pure _
  | cons item rest ih =>
      rw [List.mapM_cons]
      apply RuntimeCleanupStorage.bind (action item)
      · exact safe item
      · intro value
        apply RuntimeCleanupStorage.bind
        · exact ih
        · intro values
          exact .pure _

private theorem runtimeStorage_forInLoop (values : List α)
    (body : (value : α) → value ∈ values → β → EvalM (ForInStep β))
    (safe : ∀ value member accumulator, RuntimeCleanupStorage (body value member accumulator))
    (remaining : List α) (accumulator : β) (inside : ∃ earlier, earlier ++ remaining = values) :
    RuntimeCleanupStorage (List.forIn'.loop values body remaining accumulator inside) := by
  induction remaining generalizing accumulator with
  | nil => exact .pure _
  | cons value rest ih =>
      simp only [List.forIn'.loop]
      apply RuntimeCleanupStorage.bind
      · exact safe _ _ _
      · intro step
        cases step with
        | done accumulator => exact .pure _
        | yield accumulator => exact ih _ _

theorem RuntimeCleanupStorage.forIn (values : List α) (accumulator : β)
    (body : α → β → EvalM (ForInStep β))
    (safe : ∀ value accumulator, RuntimeCleanupStorage (body value accumulator)) :
    RuntimeCleanupStorage (forIn values accumulator body) := by
  apply runtimeStorage_forInLoop
  intro value member current
  exact safe value current

theorem RuntimeCleanupStorage.foreach (values : List α) (body : α → EvalM Unit)
    (safe : ∀ value, RuntimeCleanupStorage (body value)) :
    RuntimeCleanupStorage (do for value in values do body value) := by
  apply RuntimeCleanupStorage.bind
  · apply RuntimeCleanupStorage.forIn
    intro value member accumulator
    apply RuntimeCleanupStorage.bind (body value)
    · exact safe value
    · intro _
      exact .pure _
  · intro _
    exact .pure _

theorem materializeOwnedCarriers_storage (origin : OriginId)
    (tokens : List ExitReservationId) (carriers : List Goose.Construct.Carrier) :
    RuntimeCleanupStorage (materializeOwnedCarriers origin tokens carriers) := by
  unfold materializeOwnedCarriers
  apply RuntimeCleanupStorage.mapM
  intro carrier
  cases carrier with
  | register value => exact .of_storage_eq _ (fun _ => rfl)
  | completed destination => exact .of_storage_eq _ (fun _ => rfl)
  | pendingNamed token =>
      cases owned : tokens.contains token with
      | false => simp only [owned, ↓reduceIte]; exact .of_storage_eq _ (fun _ => rfl)
      | true =>
          simp only [owned, ↓reduceIte]
          apply RuntimeCleanupStorage.bind
          · intro state
            exact RuntimeCleanupStorage.lift origin (materializeNamedReservation token)
              (materializeNamedReservation_storage token) state
          · intro destination
            exact RuntimeCleanupStorage.pure _

private theorem borrowedExitChannelStep_storage (origin : OriginId) (carriers : List Goose.Construct.Carrier)
    (receipt : BorrowedWaitingExitReservation) :
    RuntimeCleanupStorage (borrowedExitChannelStep origin carriers receipt) := by
  unfold borrowedExitChannelStep
  dsimp only
  split <;> first | (intro state; exact ⟨[], .refl _⟩) | skip
  apply RuntimeCleanupStorage.bind
  · intro state
    exact RuntimeCleanupStorage.lift origin
      (cancelExitReservation receipt.token (carriers.filterMap fun carrier =>
        match carrier with | .completed id => some id | _ => none))
      (cancelExitReservation_storage receipt.token _) state
  · intro _ after
    apply RuntimeCleanupStorage.bind
    · intro state
      exact ⟨[], .refl _⟩
    · intro state current
      cases present : state.construction.exitReservations[receipt.token]? with
      | none =>
          simp [present, bind, Goose.Construct.fault, EvalM.stop]
          exact ⟨[], .refl _⟩
      | some reservation =>
          cases reservation with
          | restored =>
              simp only [present]
              apply RuntimeCleanupStorage.bind
              · intro currentState
                exact RuntimeCleanupStorage.lift origin (rearmExitReservation receipt)
                  (.of_storage_eq _ (rearmExitReservation_storage receipt)) currentState
              · intro _ finalState
                exact ⟨[], .refl _⟩
          | released =>
              simp [present, bind, Goose.Construct.fault, EvalM.stop]
              exact ⟨[], .refl _⟩
          | active role incoming selected snapshot =>
              simp [present, bind, pure]
              exact ⟨[], .refl _⟩
          | waiting incoming =>
              cases mismatch : incoming != receipt.incoming with
              | false =>
                  simp [present, mismatch, bind, pure]
                  exact ⟨[], .refl _⟩
              | true =>
                  simp [present, mismatch, bind, Goose.Construct.fault, EvalM.stop]
                  exact ⟨[], .refl _⟩


private theorem exitChannelCleanupToken_storage (origin : OriginId)
    (cancel : Bool) (carriers : List Goose.Construct.Carrier)
    (token : ExitReservationId) :
    RuntimeCleanupStorage (do
      if cancel then
        liftConstruction origin (cancelExitReservation token (carriers.filterMap fun carrier =>
          match carrier with | .completed id => some id | _ => none))
      liftConstruction origin (releaseExitReservation token)) := by
  cases cancel with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      intro state
      exact RuntimeCleanupStorage.lift origin (releaseExitReservation token)
        (.of_storage_eq _ (releaseExitReservation_storage token)) state
  | true =>
      simp only [↓reduceIte]
      apply RuntimeCleanupStorage.bind
      · intro state
        exact RuntimeCleanupStorage.lift origin
          (cancelExitReservation token (carriers.filterMap fun carrier =>
            match carrier with | .completed id => some id | _ => none))
          (cancelExitReservation_storage token _) state
      · intro _ after
        exact RuntimeCleanupStorage.lift origin (releaseExitReservation token)
          (.of_storage_eq _ (releaseExitReservation_storage token)) after

theorem exitChannelCleanupBorrowed_storage (origin : OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Goose.Construct.Carrier) :
    RuntimeCleanupStorage (exitChannelCleanupBorrowed origin borrowed tokens cancel carriers) := by
  unfold exitChannelCleanupBorrowed
  cases cancel with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply RuntimeCleanupStorage.foreach
      intro token
      exact exitChannelCleanupToken_storage origin false carriers token
  | true =>
      simp only [↓reduceIte]
      apply RuntimeCleanupStorage.bind
      · apply RuntimeCleanupStorage.forIn
        intro receipt current
        exact borrowedExitChannelStep_storage origin carriers receipt
      · intro _ after
        apply RuntimeCleanupStorage.bind
        · apply RuntimeCleanupStorage.forIn
          intro token member current
          apply RuntimeCleanupStorage.bind
          · intro state
            exact RuntimeCleanupStorage.lift origin
              (cancelExitReservation token (carriers.filterMap fun carrier =>
                match carrier with | .completed id => some id | _ => none))
              (cancelExitReservation_storage token _) state
          · intro _ after
            apply RuntimeCleanupStorage.bind
            · intro state
              exact RuntimeCleanupStorage.lift origin (releaseExitReservation token)
                (.of_storage_eq _ (releaseExitReservation_storage token)) state
            · intro _
              exact RuntimeCleanupStorage.pure (ForInStep.yield current)
        · intro _
          exact RuntimeCleanupStorage.pure ()

theorem RuntimeCleanupStorage.query (action : EvalM α) (query : StateQuery action) :
    RuntimeCleanupStorage action :=
  .of_storage_eq _ (fun state => congrArg (fun current => current.construction.storage) (query state))

theorem RuntimeCleanupStorage.ite (condition : Prop) [Decidable condition]
    (yes no : EvalM α) (first : RuntimeCleanupStorage yes) (second : RuntimeCleanupStorage no) :
    RuntimeCleanupStorage (if condition then yes else no) := by
  by_cases selected : condition
  · simpa only [selected, ↓reduceIte] using first
  · simpa only [selected, ↓reduceIte] using second

theorem cleanupDestination_storage (origin : OriginId) (id : DestinationId) (carriers : List Goose.Construct.Carrier) :
    RuntimeCleanupStorage (cleanupDestination origin id carriers) := by
  unfold cleanupDestination
  apply RuntimeCleanupStorage.bind
  · exact .query _ (stateQuery_getDestination id)
  · intro destination
    apply RuntimeCleanupStorage.ite
    · exact .pure ()
    · apply RuntimeCleanupStorage.bind EvalM.get
      · exact .query _ stateQuery_get
      · intro state
        cases selected : protectedReplacement? state.construction id carriers with
        | some replacement =>
            exact .lift _ _ (.of_storage_eq _ (fun current =>
              Goose.Construct.abandonPreservingExit_storage current id replacement))
        | none =>
            apply RuntimeCleanupStorage.ite
            · exact .pure ()
            · exact .lift _ _ (abandonTree_storage id)

theorem cleanupReceivingDestination_storage (origin : OriginId) (id : DestinationId)
    (carriers : List Goose.Construct.Carrier) : RuntimeCleanupStorage (cleanupReceivingDestination origin id carriers) := by
  unfold cleanupReceivingDestination
  apply RuntimeCleanupStorage.bind
  · exact .query _ (stateQuery_receivingDestination id)
  · intro selected
    exact cleanupDestination_storage origin selected carriers

theorem releaseScopeState_storage (environment : RuntimeActivation) (scope : Nat)
    (scopeInst : ScopeInst) (state : ExecutionState) :
    (releaseScopeState environment scope scopeInst state).construction.storage = state.construction.storage := rfl

theorem releaseScope_storage (environment : RuntimeActivation) (scope : Nat) (scopeInst : ScopeInst) :
    RuntimeCleanupStorage (releaseScope environment scope scopeInst) :=
  .of_storage_eq _ (fun _ => rfl)

theorem finishBorrowedExitChannels_storage (origin : OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Goose.Construct.Carrier) (result : EvalM (List Goose.Construct.Carrier))
    (remaining : RuntimeCleanupStorage result) :
    RuntimeCleanupStorage (finishBorrowedExitChannels origin borrowed tokens cancel carriers result) := by
  have source : finishBorrowedExitChannels origin borrowed tokens cancel carriers result =
      (exitChannelCleanupBorrowed origin borrowed tokens cancel carriers >>= fun _ => result) := by
    funext state
    unfold finishBorrowedExitChannels
    cases cleanup : exitChannelCleanupBorrowed origin borrowed tokens cancel carriers state with
    | ok value after => cases value; simp only [bind, cleanup]
    | stop reason after | escape address values after | jump target kind after => simp only [bind, cleanup]
  rw [source]
  exact .bind _ _ (exitChannelCleanupBorrowed_storage origin borrowed tokens cancel carriers)
    (fun _ => remaining)

theorem finishBorrowedExitChannels_ok_storage (origin : OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers result : List Goose.Construct.Carrier) :
    RuntimeCleanupStorage (finishBorrowedExitChannels origin borrowed tokens cancel carriers (.ok result)) :=
  finishBorrowedExitChannels_storage _ _ _ _ _ _ (.of_storage_eq _ (fun _ => rfl))

theorem finishBorrowedExitChannels_stop_storage (origin : OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Goose.Construct.Carrier) (reason : Goose.Core.Stop) :
    RuntimeCleanupStorage (finishBorrowedExitChannels origin borrowed tokens cancel carriers (.stop reason)) :=
  finishBorrowedExitChannels_storage _ _ _ _ _ _ (.of_storage_eq _ (fun _ => rfl))

theorem finishBorrowedExitChannels_escape_storage (origin : OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers result : List Goose.Construct.Carrier) (address : ExitAddress) :
    RuntimeCleanupStorage (finishBorrowedExitChannels origin borrowed tokens cancel carriers (.escape address result)) :=
  finishBorrowedExitChannels_storage _ _ _ _ _ _ (.of_storage_eq _ (fun _ => rfl))

theorem finishBorrowedExitChannels_jump_storage (origin : OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Goose.Construct.Carrier) (target : Nat) (kind : JumpKind) :
    RuntimeCleanupStorage (finishBorrowedExitChannels origin borrowed tokens cancel carriers (.jump target kind)) :=
  finishBorrowedExitChannels_storage _ _ _ _ _ _ (.of_storage_eq _ (fun _ => rfl))

end Goose.Proofs.ExitExecution
