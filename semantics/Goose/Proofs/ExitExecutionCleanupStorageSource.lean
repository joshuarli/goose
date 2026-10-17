import Goose.Proofs.ExitExecutionCleanupStorageFinish
import Goose.Proofs.ExitExecutionCleanupStorageObservations

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core

theorem withExitChannels_after_action_storage
    (source activation : RuntimeActivation) (operands : List Goose.Construct.Expr) (origin : OriginId)
    (action : List Channel → EvalM (List Goose.Construct.Carrier))
    (initial prepared : ExecutionState) (channels : List Channel)
    (setup : exitChannels source activation operands origin initial = .ok channels prepared) :
    ∃ changes, CleanupStorageTrace changes
      (Goose.Proofs.Exit.stepState (action channels prepared)).construction.storage
      (Goose.Proofs.Exit.stepState
        (withExitChannels source activation operands origin action initial)).construction.storage := by
  rw [withExitChannels_decomposition, setup]
  cases evaluated : action channels prepared with
  | ok raw afterOperands =>
      obtain ⟨changes, framed⟩ := materializeOwnedCarriers_storage origin
        (exitChannelReservationTokens initial.construction.exitReservations.size prepared) raw afterOperands
      cases materialized : materializeOwnedCarriers origin
          (exitChannelReservationTokens initial.construction.exitReservations.size prepared) raw afterOperands with
      | ok completed after =>
          obtain ⟨later, cleaned⟩ := finishBorrowedExitChannels_ok_storage origin
            (borrowedExitChannelReceipts activation initial)
            (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
            false completed completed after
          exact ⟨changes ++ later, .append
            (by simpa only [evaluated, materialized, Goose.Proofs.Exit.stepState] using framed)
            (by simpa only [evaluated, materialized, Goose.Proofs.Exit.stepState] using cleaned)⟩
      | stop reason after =>
          obtain ⟨later, cleaned⟩ := finishBorrowedExitChannels_stop_storage origin
            (borrowedExitChannelReceipts activation initial)
            (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
            false [] reason after
          exact ⟨changes ++ later, .append
            (by simpa only [evaluated, materialized, Goose.Proofs.Exit.stepState] using framed)
            (by simpa only [evaluated, materialized, Goose.Proofs.Exit.stepState] using cleaned)⟩
      | escape address completed after =>
          obtain ⟨later, cleaned⟩ := finishBorrowedExitChannels_escape_storage origin
            (borrowedExitChannelReceipts activation initial)
            (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
            true completed completed address after
          exact ⟨changes ++ later, .append
            (by simpa only [evaluated, materialized, Goose.Proofs.Exit.stepState] using framed)
            (by simpa only [evaluated, materialized, Goose.Proofs.Exit.stepState] using cleaned)⟩
      | jump target kind after =>
          cases kind with
          | breakValue completed =>
              obtain ⟨later, cleaned⟩ := finishBorrowedExitChannels_jump_storage origin
                (borrowedExitChannelReceipts activation initial)
                (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
                true completed target (.breakValue completed) after
              exact ⟨changes ++ later, .append
                (by simpa only [evaluated, materialized, Goose.Proofs.Exit.stepState] using framed)
                (by simpa only [evaluated, materialized, Goose.Proofs.Exit.stepState] using cleaned)⟩
          | continueLoop =>
              obtain ⟨later, cleaned⟩ := finishBorrowedExitChannels_jump_storage origin
                (borrowedExitChannelReceipts activation initial)
                (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
                true [] target .continueLoop after
              exact ⟨changes ++ later, .append
                (by simpa only [evaluated, materialized, Goose.Proofs.Exit.stepState] using framed)
                (by simpa only [evaluated, materialized, Goose.Proofs.Exit.stepState] using cleaned)⟩
  | stop reason after =>
      simpa only [evaluated, Goose.Proofs.Exit.stepState] using
        finishBorrowedExitChannels_stop_storage origin (borrowedExitChannelReceipts activation initial)
          (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
          false [] reason after
  | escape address completed after =>
      simpa only [evaluated, Goose.Proofs.Exit.stepState] using
        finishBorrowedExitChannels_escape_storage origin (borrowedExitChannelReceipts activation initial)
          (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
          true completed completed address after
  | jump target kind after =>
      cases kind with
      | breakValue completed =>
          simpa only [evaluated, Goose.Proofs.Exit.stepState] using
            finishBorrowedExitChannels_jump_storage origin (borrowedExitChannelReceipts activation initial)
              (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
              true completed target (.breakValue completed) after
      | continueLoop =>
          simpa only [evaluated, Goose.Proofs.Exit.stepState] using
            finishBorrowedExitChannels_jump_storage origin (borrowedExitChannelReceipts activation initial)
              (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
              true [] target .continueLoop after

end Goose.Proofs.ExitExecution
