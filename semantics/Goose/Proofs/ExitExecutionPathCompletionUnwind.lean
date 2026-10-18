import Goose.Proofs.ExitExecutionPathExitChannelsUnwind
import Goose.Proofs.ExitExecutionPathCompletion

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

private theorem completionCleanup_eq (origin : Goose.Core.OriginId) (tokens : List Nat)
    (cancel : Bool) (carriers : List Carrier) :
    ownershipChannelCleanup origin tokens.reverse cancel carriers =
      exitChannelCleanupBorrowed origin [] tokens cancel carriers := by
  cases cancel <;> funext state
  all_goals simp only [ownershipChannelCleanup, exitChannelCleanupBorrowed, Bool.false_eq_true,
    ↓reduceIte, List.reverse_nil, List.forIn_nil, pure_bind]
  all_goals rfl

theorem completionProduce_escape_after_child (channels : List Channel) (origin : Goose.Core.OriginId)
    (action : List Channel → EvalM (List Carrier))
    (initial prepared before : ExecutionState) (planned : List (Channel × Option Nat))
    (address : ExitAddress) (carriers : List Carrier)
    (setup : CompletionPreparation channels origin initial planned prepared)
    (escaped : action (planned.map Prod.fst) prepared = .escape address carriers before) :
    (∃ final changes,
      withCompletionChannels channels origin action initial = .escape address carriers final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) ∨
    (∃ reason final changes,
      withCompletionChannels channels origin action initial = .stop reason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) := by
  have actual := withCompletionChannels_after_escape channels origin action initial prepared before planned
    address carriers setup escaped
  simp only [finishBorrowedExitChannels] at actual
  have stdout := exitChannelCleanupBorrowed_stdout origin [] (planned.filterMap Prod.snd) true carriers before
  have objects := exitChannelCleanupBorrowed_objects origin [] (planned.filterMap Prod.snd) true carriers before
  obtain ⟨changes, storage⟩ := exitChannelCleanupBorrowed_storage origin [] (planned.filterMap Prod.snd) true carriers before
  obtain ⟨final, continued | ⟨reason, stopped⟩⟩ := ownershipChannelCleanup_control origin
    (planned.filterMap Prod.snd).reverse true carriers before
  · rw [completionCleanup_eq] at continued
    rw [continued] at actual stdout objects storage
    exact Or.inl ⟨final, changes, actual, stdout, objects, storage⟩
  · rw [completionCleanup_eq] at stopped
    rw [stopped] at actual stdout objects storage
    exact Or.inr ⟨reason, final, changes, actual, stdout, objects, storage⟩

theorem completionProduce_stop_after_child (channels : List Channel) (origin : Goose.Core.OriginId)
    (action : List Channel → EvalM (List Carrier))
    (initial prepared before : ExecutionState) (planned : List (Channel × Option Nat))
    (reason : Goose.Core.Stop)
    (setup : CompletionPreparation channels origin initial planned prepared)
    (stopped : action (planned.map Prod.fst) prepared = .stop reason before) :
    ∃ finalReason final changes,
      withCompletionChannels channels origin action initial = .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage := by
  have actual := withCompletionChannels_after_stop channels origin action initial prepared before planned
    reason setup stopped
  simp only [finishBorrowedExitChannels] at actual
  have stdout := exitChannelCleanupBorrowed_stdout origin [] (planned.filterMap Prod.snd) false [] before
  have objects := exitChannelCleanupBorrowed_objects origin [] (planned.filterMap Prod.snd) false [] before
  obtain ⟨changes, storage⟩ := exitChannelCleanupBorrowed_storage origin [] (planned.filterMap Prod.snd) false [] before
  obtain ⟨final, continued | ⟨finalReason, stoppedCleanup⟩⟩ := ownershipChannelCleanup_control origin
    (planned.filterMap Prod.snd).reverse false [] before
  · rw [completionCleanup_eq] at continued
    rw [continued] at actual stdout objects storage
    exact ⟨reason, final, changes, actual, stdout, objects, storage⟩
  · rw [completionCleanup_eq] at stoppedCleanup
    rw [stoppedCleanup] at actual stdout objects storage
    exact ⟨finalReason, final, changes, actual, stdout, objects, storage⟩

#print axioms completionProduce_stop_after_child

#print axioms completionProduce_escape_after_child

end Goose.Proofs.ExitExecution
