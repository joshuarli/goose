import Goose.Proofs.ExitExecutionPathReturns
import Goose.Proofs.ExitExecutionCleanupStorageSource
import Goose.Proofs.OwnershipAmbientContinuations

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem withExitChannels_escape_after_action (source activation : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) (action : List Channel → EvalM (List Carrier))
    (initial prepared before : ExecutionState) (channels : List Channel)
    (address : ExitAddress) (carriers : List Carrier)
    (setup : exitChannels source activation operands origin initial = .ok channels prepared)
    (escaped : action channels prepared = .escape address carriers before) :
    (∃ final changes,
      withExitChannels source activation operands origin action initial = .escape address carriers final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) ∨
    (∃ reason final changes,
      withExitChannels source activation operands origin action initial = .stop reason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) := by
  have actual := withExitChannels_ownership_continuation source activation operands origin action initial
  rw [setup] at actual
  simp only [bind, escaped, finishOwnershipExitChannels] at actual
  obtain ⟨final, continued | ⟨reason, stopped⟩⟩ := runOwnershipExitContinuation_retains origin
    (borrowedOwnershipExitReceipts activation initial)
    (newOwnershipExitTokens initial.construction.exitReservations.size prepared)
    (.escaped address carriers) before
  · have returned : withExitChannels source activation operands origin action initial = .escape address carriers final :=
      actual.trans continued
    have frame := withExitChannels_after_action_frame source activation operands origin action initial prepared channels setup
    obtain ⟨changes, storage⟩ := withExitChannels_after_action_storage source activation operands origin action initial prepared channels setup
    rw [escaped, returned] at frame storage
    exact Or.inl ⟨final, changes, returned, frame.1, frame.2, storage⟩
  · have returned : withExitChannels source activation operands origin action initial = .stop reason final :=
      actual.trans stopped
    have frame := withExitChannels_after_action_frame source activation operands origin action initial prepared channels setup
    obtain ⟨changes, storage⟩ := withExitChannels_after_action_storage source activation operands origin action initial prepared channels setup
    rw [escaped, returned] at frame storage
    exact Or.inr ⟨reason, final, changes, returned, frame.1, frame.2, storage⟩

theorem withExitChannels_stop_after_action (source activation : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) (action : List Channel → EvalM (List Carrier))
    (initial prepared before : ExecutionState) (channels : List Channel) (reason : Goose.Core.Stop)
    (setup : exitChannels source activation operands origin initial = .ok channels prepared)
    (stopped : action channels prepared = .stop reason before) :
    ∃ finalReason final changes,
      withExitChannels source activation operands origin action initial = .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage := by
  have actual := withExitChannels_ownership_continuation source activation operands origin action initial
  rw [setup] at actual
  simp only [bind, stopped, finishOwnershipExitChannels] at actual
  obtain ⟨final, continued | ⟨finalReason, stoppedCleanup⟩⟩ := runOwnershipExitContinuation_retains origin
    (borrowedOwnershipExitReceipts activation initial)
    (newOwnershipExitTokens initial.construction.exitReservations.size prepared)
    (.stopped reason) before
  · have returned : withExitChannels source activation operands origin action initial = .stop reason final :=
      actual.trans continued
    have frame := withExitChannels_after_action_frame source activation operands origin action initial prepared channels setup
    obtain ⟨changes, storage⟩ := withExitChannels_after_action_storage source activation operands origin action initial prepared channels setup
    rw [stopped, returned] at frame storage
    exact ⟨reason, final, changes, returned, frame.1, frame.2, storage⟩
  · have returned : withExitChannels source activation operands origin action initial = .stop finalReason final :=
      actual.trans stoppedCleanup
    have frame := withExitChannels_after_action_frame source activation operands origin action initial prepared channels setup
    obtain ⟨changes, storage⟩ := withExitChannels_after_action_storage source activation operands origin action initial prepared channels setup
    rw [stopped, returned] at frame storage
    exact ⟨finalReason, final, changes, returned, frame.1, frame.2, storage⟩

#print axioms withExitChannels_escape_after_action
#print axioms withExitChannels_stop_after_action

end Goose.Proofs.ExitExecution
