import Goose.Proofs.ConstructionActivationCounterOwner

namespace Goose.Proofs.ConstructionActivationCounterExit
open Goose.Construct Goose.Proofs.ConstructionActivationCounter Goose.Proofs.ConstructionActivationCounterOwner
open Goose.Proofs.ExitExecution

theorem counter_exitChannelPreparation (source activation : RuntimeActivation)
    (origin : Goose.Core.OriginId) (channel : Channel × Expr) :
    PreservesActivationCounter (exitChannelPreparation source activation origin channel) := by
  rcases channel with ⟨channel, operand⟩
  cases channel with
  | register ty => exact counter_pure _
  | construct incoming =>
      unfold exitChannelPreparation
      apply counter_bind
      · exact counter_stateQuery _ (stateQuery_exitSource source incoming operand)
      · intro kind
        apply counter_bind
        · exact counter_lift _ _
        · intro _; exact counter_pure _
  | completion token =>
      unfold exitChannelPreparation
      apply counter_bind
      · exact counter_get
      · intro state
        cases present : state.construction.exitReservations[token]? with
        | none => exact counter_stop _
        | some reservation =>
            cases reservation with
            | waiting incoming => exact counter_pure _
            | active role incoming selected snapshot =>
                apply counter_bind
                · exact counter_receivingDestination selected
                · intro current
                  apply counter_bind
                  · exact counter_stateQuery _ (stateQuery_exitSource source current operand)
                  · intro kind
                    apply counter_bind
                    · exact counter_lift _ _
                    · intro _; exact counter_pure _
            | restored | released => exact counter_stop _

theorem counter_exitChannels (source activation : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) : PreservesActivationCounter (exitChannels source activation operands origin) := by
  unfold exitChannels
  split
  · exact counter_stop _
  · apply counter_listMapM
    intro item
    exact counter_exitChannelPreparation source activation origin item

theorem counter_exitChannelCleanup (origin : Goose.Core.OriginId)
    (tokens : List ExitReservationId) (cancel : Bool) (carriers : List Carrier) :
    PreservesActivationCounter (exitChannelCleanup origin tokens cancel carriers) := by
  unfold exitChannelCleanup
  cases cancel with
  | false =>
      apply counter_bind
      · apply counter_listForIn
        intro token _
        apply counter_bind
        · exact counter_lift _ _
        · intro _; exact counter_pure _
      · intro _; exact counter_pure _
  | true =>
      apply counter_bind
      · apply counter_listForIn
        intro token _
        apply counter_bind
        · exact counter_lift _ _
        · intro _
          apply counter_bind
          · exact counter_lift _ _
          · intro _; exact counter_pure _
      · intro _; exact counter_pure _

theorem counter_borrowedExitChannelStep (origin : Goose.Core.OriginId)
    (carriers : List Carrier) (receipt : BorrowedWaitingExitReservation) :
    PreservesActivationCounter (borrowedExitChannelStep origin carriers receipt) := by
  unfold borrowedExitChannelStep
  dsimp only
  split <;> first | exact counter_pure _ | skip
  apply counter_bind
  · exact counter_lift _ _
  · intro _
    apply counter_bind
    · exact counter_get
    · intro state
      cases state.construction.exitReservations[receipt.token]? with
      | none => exact counter_stop _
      | some reservation =>
          cases reservation with
          | restored =>
              apply counter_bind
              · exact counter_lift _ _
              · intro _; exact counter_pure _
          | released => exact counter_stop _
          | active role incoming selected snapshot => exact counter_pure _
          | waiting incoming =>
              dsimp only
              split
              · exact counter_stop _
              · exact counter_pure _


theorem counter_exitChannelCleanupBorrowed (origin : Goose.Core.OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Carrier) :
    PreservesActivationCounter (exitChannelCleanupBorrowed origin borrowed tokens cancel carriers) := by
  unfold exitChannelCleanupBorrowed
  cases cancel with
  | false => exact counter_exitChannelCleanup origin tokens false carriers
  | true =>
      apply counter_bind
      · apply counter_listForIn
        intro receipt _
        exact counter_borrowedExitChannelStep origin carriers receipt
      · intro _
        exact counter_exitChannelCleanup origin tokens true carriers


theorem counter_finishBorrowedExitChannels (origin : Goose.Core.OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Carrier) (result : ExecutionState → ExecutionStep (List Carrier))
    (frame : ∀ state, Goose.Proofs.Exit.stepState (result state) = state) :
    PreservesActivationCounter (finishBorrowedExitChannels origin borrowed tokens cancel carriers result) := by
  intro state
  have prior := counter_exitChannelCleanupBorrowed origin borrowed tokens cancel carriers state
  unfold finishBorrowedExitChannels
  cases cleaned : exitChannelCleanupBorrowed origin borrowed tokens cancel carriers state with
  | ok value final =>
    cases value
    simp only [cleaned, Goose.Proofs.Exit.stepState] at prior
    rw [frame]
    exact prior
  | stop reason final | escape address values final | jump target kind final =>
    simpa only [cleaned, Goose.Proofs.Exit.stepState] using prior

theorem counter_withExitChannels (source activation : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) (action : List Channel → EvalM (List Carrier))
    (preserved : ∀ channels, PreservesActivationCounter (action channels)) :
    PreservesActivationCounter (withExitChannels source activation operands origin action) := by
  intro state
  rw [withExitChannels_decomposition source activation operands origin action state]
  have initial := counter_exitChannels source activation operands origin state
  cases preflight : exitChannels source activation operands origin state with
  | stop reason final | escape address carriers final | jump target kind final =>
    simpa [preflight, Goose.Proofs.Exit.stepState] using initial
  | ok channels prepared =>
    simp only [preflight, Goose.Proofs.Exit.stepState] at initial
    have actionBound := preserved channels prepared
    cases evaluation : action channels prepared with
    | ok carriers after =>
      simp only [evaluation, Goose.Proofs.Exit.stepState] at actionBound
      let tokens := exitChannelReservationTokens state.construction.exitReservations.size prepared
      have materializedBound := counter_materializeOwnedCarriers origin tokens carriers after
      cases materialized : materializeOwnedCarriers origin tokens carriers after with
      | ok completed final =>
        simp only [materialized, Goose.Proofs.Exit.stepState] at materializedBound
        have finish := counter_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state) tokens
          false completed (.ok completed) (fun _ => rfl) final
        simpa [preflight, evaluation, materialized, tokens] using
          Nat.le_trans initial (Nat.le_trans actionBound (Nat.le_trans materializedBound finish))
      | stop reason final =>
        simp only [materialized, Goose.Proofs.Exit.stepState] at materializedBound
        have finish := counter_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state) tokens
          false [] (.stop reason) (fun _ => rfl) final
        simpa [preflight, evaluation, materialized, tokens] using
          Nat.le_trans initial (Nat.le_trans actionBound (Nat.le_trans materializedBound finish))
      | escape address completed final =>
        simp only [materialized, Goose.Proofs.Exit.stepState] at materializedBound
        have finish := counter_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state) tokens
          true completed (.escape address completed) (fun _ => rfl) final
        simpa [preflight, evaluation, materialized, tokens] using
          Nat.le_trans initial (Nat.le_trans actionBound (Nat.le_trans materializedBound finish))
      | jump target kind final =>
        simp only [materialized, Goose.Proofs.Exit.stepState] at materializedBound
        cases kind with
        | breakValue completed =>
          have finish := counter_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state) tokens
            true completed (.jump target (.breakValue completed)) (fun _ => rfl) final
          simpa [preflight, evaluation, materialized, tokens] using
            Nat.le_trans initial (Nat.le_trans actionBound (Nat.le_trans materializedBound finish))
        | continueLoop =>
          have finish := counter_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state) tokens
            true [] (.jump target .continueLoop) (fun _ => rfl) final
          simpa [preflight, evaluation, materialized, tokens] using
            Nat.le_trans initial (Nat.le_trans actionBound (Nat.le_trans materializedBound finish))
    | stop reason final =>
      simp only [evaluation, Goose.Proofs.Exit.stepState] at actionBound
      have finish := counter_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state)
        (exitChannelReservationTokens state.construction.exitReservations.size prepared) false [] (.stop reason) (fun _ => rfl) final
      simpa [preflight, evaluation] using Nat.le_trans initial (Nat.le_trans actionBound finish)
    | escape address carriers final =>
      simp only [evaluation, Goose.Proofs.Exit.stepState] at actionBound
      have finish := counter_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state)
        (exitChannelReservationTokens state.construction.exitReservations.size prepared) true carriers (.escape address carriers) (fun _ => rfl) final
      simpa [preflight, evaluation] using Nat.le_trans initial (Nat.le_trans actionBound finish)
    | jump target kind final =>
      simp only [evaluation, Goose.Proofs.Exit.stepState] at actionBound
      cases kind with
      | breakValue carriers =>
        have finish := counter_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state)
          (exitChannelReservationTokens state.construction.exitReservations.size prepared) true carriers (.jump target (.breakValue carriers)) (fun _ => rfl) final
        simpa [preflight, evaluation] using Nat.le_trans initial (Nat.le_trans actionBound finish)
      | continueLoop =>
        have finish := counter_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state)
          (exitChannelReservationTokens state.construction.exitReservations.size prepared) true [] (.jump target .continueLoop) (fun _ => rfl) final
        simpa [preflight, evaluation] using Nat.le_trans initial (Nat.le_trans actionBound finish)

#print axioms counter_withExitChannels
#print axioms counter_exitChannels
#print axioms counter_exitChannelCleanupBorrowed
end Goose.Proofs.ConstructionActivationCounterExit
