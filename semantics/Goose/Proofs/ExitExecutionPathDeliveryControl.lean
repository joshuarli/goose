import Goose.Proofs.ExitExecutionPathExitChannelsUnwind
import Goose.Proofs.ConstructionDeliveryFlowSoundnessNoJumpsOwners

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionDelivery

private theorem neverJumps_materializeOwnedCarriers (origin : Goose.Core.OriginId)
    (tokens : List Nat) (carriers : List Carrier) :
    NeverJumps (materializeOwnedCarriers origin tokens carriers) := by
  unfold materializeOwnedCarriers
  apply neverJumps_listMapM
  intro carrier
  cases carrier <;> try exact neverJumps_pure _
  case pendingNamed token =>
    apply neverJumps_conditional
    · apply neverJumps_bind
      · exact neverJumps_lift _ _
      · intro value
        exact neverJumps_pure _
    · exact neverJumps_pure _

theorem withExitChannels_ok_after_action (source activation : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) (action : List Channel → EvalM (List Carrier))
    (initial prepared before : ExecutionState) (channels : List Channel) (raw : List Carrier)
    (setup : exitChannels source activation operands origin initial = .ok channels prepared)
    (evaluated : action channels prepared = .ok raw before) :
    (∃ completed final changes,
      withExitChannels source activation operands origin action initial = .ok completed final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) ∨
    (∃ reason final changes,
      withExitChannels source activation operands origin action initial = .stop reason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) := by
  have control : ∃ final,
      (∃ completed, withExitChannels source activation operands origin action initial = .ok completed final) ∨
      ∃ reason, withExitChannels source activation operands origin action initial = .stop reason final := by
    have actual := withExitChannels_ownership_continuation source activation operands origin action initial
    rw [setup] at actual
    cases materialized : materializeOwnedCarriers origin
        (newOwnershipExitTokens initial.construction.exitReservations.size prepared) raw before with
    | ok completed after =>
        simp only [bind, evaluated, materialized, finishOwnershipExitChannels] at actual
        obtain ⟨final, continued | ⟨reason, stopped⟩⟩ := runOwnershipExitContinuation_retains origin
          (borrowedOwnershipExitReceipts activation initial)
          (newOwnershipExitTokens initial.construction.exitReservations.size prepared)
          (.completed completed) after
        · exact ⟨final, Or.inl ⟨completed, actual.trans continued⟩⟩
        · exact ⟨final, Or.inr ⟨reason, actual.trans stopped⟩⟩
    | stop reason after =>
        simp only [bind, evaluated, materialized, finishOwnershipExitChannels] at actual
        obtain ⟨final, continued | ⟨finalReason, stopped⟩⟩ := runOwnershipExitContinuation_retains origin
          (borrowedOwnershipExitReceipts activation initial)
          (newOwnershipExitTokens initial.construction.exitReservations.size prepared)
          (.stopped reason) after
        · exact ⟨final, Or.inr ⟨reason, actual.trans continued⟩⟩
        · exact ⟨final, Or.inr ⟨finalReason, actual.trans stopped⟩⟩
    | escape address values after =>
        exact False.elim (materializeOwnedCarriers_no_escape origin _ raw before address values after materialized)
    | jump target kind after =>
        exact False.elim (neverJumps_materializeOwnedCarriers origin _ raw before target kind after materialized)
  obtain ⟨final, ⟨completed, returned⟩ | ⟨reason, returned⟩⟩ := control
  · have frame := withExitChannels_after_action_frame source activation operands origin action initial prepared channels setup
    obtain ⟨changes, storage⟩ := withExitChannels_after_action_storage source activation operands origin action initial prepared channels setup
    rw [evaluated, returned] at frame storage
    exact Or.inl ⟨completed, final, changes, returned, frame.1, frame.2, storage⟩
  · have frame := withExitChannels_after_action_frame source activation operands origin action initial prepared channels setup
    obtain ⟨changes, storage⟩ := withExitChannels_after_action_storage source activation operands origin action initial prepared channels setup
    rw [evaluated, returned] at frame storage
    exact Or.inr ⟨reason, final, changes, returned, frame.1, frame.2, storage⟩

#print axioms withExitChannels_ok_after_action

end Goose.Proofs.ExitExecution
