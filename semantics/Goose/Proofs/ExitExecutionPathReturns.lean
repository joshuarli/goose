import Goose.Proofs.ExitExecutionPath

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem finishBorrowedExitChannels_after_action_frame
    (origin : Goose.Core.OriginId) (borrowed : List BorrowedWaitingExitReservation)
    (tokens : List ExitReservationId) (cancel : Bool) (carriers : List Carrier)
    (result : ExecutionState → ExecutionStep (List Carrier))
    (query : ∀ state, Goose.Proofs.Exit.stepState (result state) = state)
    (initial : ExecutionState) :
    let final := Goose.Proofs.Exit.stepState
      (finishBorrowedExitChannels origin borrowed tokens cancel carriers result initial)
    final.construction.stdout = initial.construction.stdout ∧ final.objects = initial.objects := by
  have stdout := exitChannelCleanupBorrowed_stdout origin borrowed tokens cancel carriers initial
  have objects := exitChannelCleanupBorrowed_objects origin borrowed tokens cancel carriers initial
  unfold finishBorrowedExitChannels
  cases cleaned : exitChannelCleanupBorrowed origin borrowed tokens cancel carriers initial <;>
    simp only [cleaned, Goose.Proofs.Exit.stepState] at stdout objects ⊢
  all_goals first
    | exact ⟨stdout, objects⟩
    | change (Goose.Proofs.Exit.stepState (result _)).construction.stdout = _ ∧
          (Goose.Proofs.Exit.stepState (result _)).objects = _
      rw [query]; exact ⟨stdout, objects⟩

theorem withExitChannels_after_action_frame
    (source activation : RuntimeActivation) (operands : List Expr) (origin : Goose.Core.OriginId)
    (action : List Channel → EvalM (List Carrier))
    (initial prepared : ExecutionState) (channels : List Channel)
    (setup : exitChannels source activation operands origin initial = .ok channels prepared) :
    let afterOperands := Goose.Proofs.Exit.stepState (action channels prepared)
    let final := Goose.Proofs.Exit.stepState
      (withExitChannels source activation operands origin action initial)
    final.construction.stdout = afterOperands.construction.stdout ∧ final.objects = afterOperands.objects := by
  rw [withExitChannels_decomposition, setup]
  cases evaluated : action channels prepared with
  | ok raw afterOperands =>
      have stdout := materializeOwnedCarriers_stdout origin
        (exitChannelReservationTokens initial.construction.exitReservations.size prepared) raw afterOperands
      have objects := materializeOwnedCarriers_objects origin
        (exitChannelReservationTokens initial.construction.exitReservations.size prepared) raw afterOperands
      cases materialized : materializeOwnedCarriers origin
          (exitChannelReservationTokens initial.construction.exitReservations.size prepared) raw afterOperands with
      | ok completed after =>
          simp only [evaluated, materialized, Goose.Proofs.Exit.stepState] at stdout objects ⊢
          obtain ⟨cleanupStdout, cleanupObjects⟩ := finishBorrowedExitChannels_after_action_frame
            origin (borrowedExitChannelReceipts activation initial)
            (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
            false completed (.ok completed) (fun _ => rfl) after
          exact ⟨cleanupStdout.trans stdout, cleanupObjects.trans objects⟩
      | stop reason after =>
          simp only [evaluated, materialized, Goose.Proofs.Exit.stepState] at stdout objects ⊢
          obtain ⟨cleanupStdout, cleanupObjects⟩ := finishBorrowedExitChannels_after_action_frame
            origin (borrowedExitChannelReceipts activation initial)
            (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
            false [] (.stop reason) (fun _ => rfl) after
          exact ⟨cleanupStdout.trans stdout, cleanupObjects.trans objects⟩
      | escape address completed after =>
          simp only [evaluated, materialized, Goose.Proofs.Exit.stepState] at stdout objects ⊢
          obtain ⟨cleanupStdout, cleanupObjects⟩ := finishBorrowedExitChannels_after_action_frame
            origin (borrowedExitChannelReceipts activation initial)
            (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
            true completed (.escape address completed) (fun _ => rfl) after
          exact ⟨cleanupStdout.trans stdout, cleanupObjects.trans objects⟩
      | jump target kind after =>
          cases kind with
          | breakValue completed =>
              simp only [evaluated, materialized, Goose.Proofs.Exit.stepState] at stdout objects ⊢
              obtain ⟨cleanupStdout, cleanupObjects⟩ := finishBorrowedExitChannels_after_action_frame
                origin (borrowedExitChannelReceipts activation initial)
                (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
                true completed (.jump target (.breakValue completed)) (fun _ => rfl) after
              exact ⟨cleanupStdout.trans stdout, cleanupObjects.trans objects⟩
          | continueLoop =>
              simp only [evaluated, materialized, Goose.Proofs.Exit.stepState] at stdout objects ⊢
              obtain ⟨cleanupStdout, cleanupObjects⟩ := finishBorrowedExitChannels_after_action_frame
                origin (borrowedExitChannelReceipts activation initial)
                (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
                true [] (.jump target (.continueLoop)) (fun _ => rfl) after
              exact ⟨cleanupStdout.trans stdout, cleanupObjects.trans objects⟩
  | stop reason afterOperands =>
      simp only [evaluated, Goose.Proofs.Exit.stepState]
      exact finishBorrowedExitChannels_after_action_frame
        origin (borrowedExitChannelReceipts activation initial)
        (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
        false [] (.stop reason) (fun _ => rfl) afterOperands
  | escape address carriers afterOperands =>
      simp only [evaluated, Goose.Proofs.Exit.stepState]
      exact finishBorrowedExitChannels_after_action_frame
        origin (borrowedExitChannelReceipts activation initial)
        (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
        true carriers (.escape address carriers) (fun _ => rfl) afterOperands
  | jump target kind afterOperands =>
      cases kind with
      | breakValue completed =>
          simp only [evaluated, Goose.Proofs.Exit.stepState]
          exact finishBorrowedExitChannels_after_action_frame
            origin (borrowedExitChannelReceipts activation initial)
            (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
            true completed (.jump target (.breakValue completed)) (fun _ => rfl) afterOperands
      | continueLoop =>
          simp only [evaluated, Goose.Proofs.Exit.stepState]
          exact finishBorrowedExitChannels_after_action_frame
            origin (borrowedExitChannelReceipts activation initial)
            (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
            true [] (.jump target (.continueLoop)) (fun _ => rfl) afterOperands

#print axioms withExitChannels_after_action_frame

theorem returnFrom_after_operands_frame (fuel : Nat) (config : EvalConfig)
    (environment activation : RuntimeActivation) (targetId : Nat) (operands : List Expr)
    (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (channels : List Channel)
    (selected : targetActivation config targetId initial = .ok activation initial)
    (setup : exitChannels environment activation operands origin initial = .ok channels prepared) :
    let afterOperands := Goose.Proofs.Exit.stepState (evalOperands fuel config environment channels operands prepared)
    let final := Goose.Proofs.Exit.stepState
      (execStmt (fuel + 1) config environment (.returnFrom targetId operands origin) initial)
    final.construction.stdout = afterOperands.construction.stdout ∧ final.objects = afterOperands.objects := by
  have framed := withExitChannels_after_action_frame environment activation operands origin
    (fun channels => evalOperands fuel config environment channels operands) initial prepared channels setup
  simp only [execStmt, bind, selected]
  cases result : withExitChannels environment activation operands origin
      (fun channels => evalOperands fuel config environment channels operands) initial <;>
    simpa only [result, Goose.Proofs.Exit.stepState, Goose.Construct.escaped] using framed

#print axioms returnFrom_after_operands_frame


theorem returnFromForward_after_operands_frame (fuel : Nat) (config : EvalConfig)
    (environment activation : RuntimeActivation) (targetId : Nat) (producer : Expr)
    (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (channels : List Channel)
    (selected : targetActivation config targetId initial = .ok activation initial)
    (setup : exitChannels environment activation (List.replicate activation.channels.length producer) origin initial = .ok channels prepared) :
    let afterOperands := Goose.Proofs.Exit.stepState (evalProduce fuel config environment channels producer prepared)
    let final := Goose.Proofs.Exit.stepState
      (execStmt (fuel + 1) config environment (.returnFromForward targetId producer origin) initial)
    final.construction.stdout = afterOperands.construction.stdout ∧ final.objects = afterOperands.objects := by
  have framed := withExitChannels_after_action_frame environment activation (List.replicate activation.channels.length producer) origin
    (fun channels => evalProduce fuel config environment channels producer) initial prepared channels setup
  simp only [execStmt, bind, selected]
  cases result : withExitChannels environment activation (List.replicate activation.channels.length producer) origin
      (fun channels => evalProduce fuel config environment channels producer) initial <;>
    simpa only [result, Goose.Proofs.Exit.stepState, Goose.Construct.escaped] using framed

#print axioms returnFromForward_after_operands_frame

end Goose.Proofs.ExitExecution
