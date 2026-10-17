import Goose.Lower.Validation.SummaryPreservationReplayLoopsControl
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes
import Goose.Lower.Validation.SummaryPreservationReturnTransfer

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

private theorem fork_returns (condition : ValueId) : ReturnFrameRun (fork condition) :=
  .of_absence (fun _ => ReturnFrames.returnAbsent_fork condition)

private theorem setCur_returns (current : Option BlockId) : ReturnFrameRun (Goose.Lower.setCur current) :=
  .of_absence (fun _ => ReturnFrames.returnAbsent_setCur current)

theorem native_loopBody_stages {vt : Array (Option VTy)} {condition : ValueId}
    {body : Nat → BlockId → B ValueId} {back : B Unit} {le : LEnv} {initial : LS}
    (generated : GeneratedBuilderState initial)
    (native : NativeRows vt (Goose.Lower.loopBody condition body back le initial).2)
    (backTypes : TypeRun back) (backReturns : ReturnFrameRun back) :
    let split := fork condition le initial
    let started := ReplayBuilder.loopBodyEntry condition le initial
    let produced := body initial.stack.length split.1.2 le started
    GeneratedBuilderState started ∧ NativeRows vt produced.2 ∧
      ReturnMembershipFrame initial started ∧
      ReturnMembershipFrame produced.2 (Goose.Lower.loopBody condition body back le initial).2 := by
  dsimp only
  let split := fork condition le initial
  let started := ReplayBuilder.loopBodyEntry condition le initial
  let produced := body initial.stack.length split.1.2 le started
  let backed := back le produced.2
  have ids := fork_ids (show fork condition le initial = (split.1, split.2) from rfl)
  have bodyBound : split.1.1 < split.2.blocks.size := by
    rw [ids.1, ids.2]
    exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
  have splitGenerated := generated.fork condition (rfl : fork condition le initial = split)
  have startedGenerated := splitGenerated.setCur (some split.1.1)
    (by intro block same; cases same; exact bodyBound)
    (rfl : Goose.Lower.setCur (some split.1.1) le split.2 = ((), started))
  have whole : Goose.Lower.loopBody condition body back le initial =
      Goose.Lower.setCur (some split.1.2) le backed.2 := by
    simp only [Goose.Lower.loopBody, bind_run, get_apply]
    rfl
  have producedNative : NativeRows vt produced.2 := by
    apply native.of_prefix
    rw [whole]
    exact (backTypes le produced.2 backed.1 backed.2 rfl).trans
      (types_setCur (some split.1.2) le backed.2 _ _ rfl)
  have prefixReturns : ReturnMembershipFrame initial started :=
    (fork_returns condition le initial split.1 split.2 rfl).trans
      (setCur_returns (some split.1.1) le split.2 () started rfl)
  have suffixReturns : ReturnMembershipFrame produced.2 (Goose.Lower.loopBody condition body back le initial).2 := by
    rw [whole]
    exact (backReturns le produced.2 backed.1 backed.2 rfl).trans
      (setCur_returns (some split.1.2) le backed.2 _ _ rfl)
  exact ⟨startedGenerated, producedNative, prefixReturns, suffixReturns⟩

theorem native_loopBody_entry_stack (condition : ValueId) (le : LEnv) (state : LS) :
    (ReplayBuilder.loopBodyEntry condition le state).stack = state.stack := by
  change (fork condition le state).2.stack = state.stack
  exact (advB_fork condition le state _ _ rfl).stack

#print axioms native_loopBody_stages

end Goose.Lower.Validation.SummaryPreservation
