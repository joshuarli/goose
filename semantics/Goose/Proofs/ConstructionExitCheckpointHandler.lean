import Goose.Proofs.ConstructionExitCheckpointBranch
import Goose.Proofs.ExitExecutionPathOutsideScopeReads
import Goose.Proofs.ConstructionExitOutsideUnwind

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ExitExecution
open Goose.Proofs.ExitExecutionChecks

def recursiveOuterActivation : RuntimeActivation := { recursiveCheckpointTarget with scopes := [] }

def recursiveOuterEntered : ExecutionState := { recursiveBeforeBranch with
  construction := { recursiveBeforeBranch.construction with storage := recursiveBeforeBranch.construction.storage.extract 0 3 }
  objects := recursiveBeforeBranch.objects.drop 1
  objectOrdinals := recursiveBeforeBranch.objectOrdinals.drop 1
  nextScope := 3
  activations := recursiveBeforeBranch.activations.map (fun current => if current.act == 2 then
    { current with scopes := [] } else current) }

def recursiveOuterElse : Block := .mk 2
  [.letS 1 (.call 1 [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] 0) 0,
    .print [.view (.of (.var 1))] 0, .retValues [.bytes array [65] 0] 0] none

def recursiveOuterBody : Block :=
  .mk 0 [.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0] none

theorem recursive_checkpoint_outer_handler :
    ∃ after final : ExecutionState,
      enterActivation 16 recursiveCheckpointConfig recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody 0 recursiveOuterEntered =
        .ok [.completed 1] final ∧
      final.construction.stdout = after.construction.stdout ∧
      (∀ entry : Goose.Core.RootInst × Value,
        (Goose.Proofs.Exit.runtimeScopeRoots recursiveHelperActivation 0 recursiveHelperEntered.nextScope).contains entry.1 = false →
        (Goose.Proofs.Exit.runtimeScopeRoots recursiveCheckpointTarget 1 recursiveBeforeBranch.nextScope).contains entry.1 = false →
        (Goose.Proofs.Exit.runtimeScopeRoots recursiveOuterActivation 0 recursiveOuterEntered.nextScope).contains entry.1 = false →
        (entry ∈ final.objects ↔ entry ∈ after.objects)) ∧
      ∀ (location : Goose.Core.Loc) (fuel : Nat),
        (Goose.Proofs.Exit.runtimeScopeRoots recursiveHelperActivation 0 recursiveHelperEntered.nextScope).contains location.root = false →
        (Goose.Proofs.Exit.runtimeScopeRoots recursiveCheckpointTarget 1 recursiveBeforeBranch.nextScope).contains location.root = false →
        (Goose.Proofs.Exit.runtimeScopeRoots recursiveOuterActivation 0 recursiveOuterEntered.nextScope).contains location.root = false →
        mapStepState (fun _ => ExecutionState.initial) (readLoc fuel recursiveCheckpointConfig.layout location final) =
        mapStepState (fun _ => ExecutionState.initial) (readLoc fuel recursiveCheckpointConfig.layout location after) := by
  obtain ⟨after, branch, landed⟩ := recursive_checkpoint_branch_escape (some recursiveOuterElse)
  let cleaned := { after with construction := { after.construction with
    exitReservations := after.construction.exitReservations.set! 0 .released } }
  let innerUnwound := releaseScopeState recursiveHelperActivation 0 recursiveHelperEntered.nextScope cleaned
  let crossed := { innerUnwound with activations := innerUnwound.activations.filter (fun current => current.act != recursiveHelperActivation.act) }
  let branchUnwound := releaseScopeState recursiveCheckpointTarget 1 recursiveBeforeBranch.nextScope crossed
  let outerUnwound := releaseScopeState recursiveOuterActivation 0 recursiveOuterEntered.nextScope branchUnwound
  let final := { outerUnwound with activations := outerUnwound.activations.filter (fun current => current.act != recursiveOuterActivation.act) }
  have binding : bindAll recursiveOuterActivation.act recursiveOuterEntered.nextScope [(0, .int .i64 0)] { recursiveOuterEntered with
      nextScope := recursiveOuterEntered.nextScope + 1
      activations := recursiveOuterEntered.activations.map (fun current => if current.act == recursiveOuterActivation.act then
        { current with scopes := (0, recursiveOuterEntered.nextScope) :: recursiveOuterActivation.scopes } else current) } =
      .ok () recursiveBeforeBranch := by cbv
  have environmentEq : { recursiveOuterActivation with scopes := (0, recursiveOuterEntered.nextScope) :: recursiveOuterActivation.scopes } =
      recursiveCheckpointTarget := by cbv
  have statements : execStmts 14 recursiveCheckpointConfig recursiveCheckpointTarget
      [.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0] recursiveBeforeBranch =
      .escape ⟨2, .nonlocal 0⟩ [.completed 1] branchUnwound := by
    simp only [execStmts, bind, branch]
    rfl
  have body : execActivationBody 15 recursiveCheckpointConfig recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody recursiveOuterEntered =
      .escape ⟨2, .nonlocal 0⟩ [.completed 1] outerUnwound := by
    unfold execActivationBody execResultScope
    have fresh : freshScope = fun state => .ok state.nextScope { state with nextScope := state.nextScope + 1 } := by
      funext state
      rfl
    rw [fresh]
    simp only [recursiveOuterBody, bind, EvalM.get, EvalM.set, withScope, binding, environmentEq, statements, releaseScope]
    rfl
  have lookup : recursiveCheckpointConfig.module.impls[recursiveOuterActivation.implementation]?.map (fun impl => impl.results.toList.map (·.ty)) =
      some [.varr (.int .u8)] := by cbv
  have finalLanded : LandedResultChannels final [.construct 1] [.varr (.int .u8)] [.completed 1] :=
    LandedResultChannels.of_construction_eq (before := cleaned) (after := final) rfl landed
  have finish := finalLanded.finishChannels recursiveCheckpointConfig.layout 0
  have matched : enterActivation 16 recursiveCheckpointConfig recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody 0 recursiveOuterEntered =
      .ok [.completed 1] final := by
    have implFound : recursiveCheckpointConfig.module.impls[recursiveOuterActivation.implementation]? =
        some ⟨"builder", #[⟨0, .byValue⟩], #[⟨array, .value, none⟩], recursiveOuterActivation.vars, recursiveOuterBody,
          .known ⟨[], [], [], [], [], [0], [], [], true, true⟩⟩ := by cbv
    simp only [enterActivation]
    rw [implFound]
    simp only [finishActivation, body]
    simp only [recursiveOuterActivation, recursiveCheckpointTarget, beq_self_eq_true, ↓reduceIte]
    simp only [List.map_cons, List.map_nil, array]
    dsimp only [final, recursiveOuterActivation, recursiveCheckpointTarget] at finish
    rw [finish]
    rfl
  refine ⟨after, final, matched, rfl, ?_, ?_⟩
  · intro entry innerOutside branchOutside outerOutside
    change entry ∈ (releaseScopeState recursiveOuterActivation 0 recursiveOuterEntered.nextScope branchUnwound).objects ↔ entry ∈ after.objects
    rw [Goose.Proofs.Exit.runtime_release_scope_outside recursiveOuterActivation 0 recursiveOuterEntered.nextScope branchUnwound entry outerOutside]
    change entry ∈ (releaseScopeState recursiveCheckpointTarget 1 recursiveBeforeBranch.nextScope crossed).objects ↔ entry ∈ after.objects
    rw [Goose.Proofs.Exit.runtime_release_scope_outside recursiveCheckpointTarget 1 recursiveBeforeBranch.nextScope crossed entry branchOutside]
    change entry ∈ (releaseScopeState recursiveHelperActivation 0 recursiveHelperEntered.nextScope cleaned).objects ↔ entry ∈ after.objects
    rw [Goose.Proofs.Exit.runtime_release_scope_outside recursiveHelperActivation 0 recursiveHelperEntered.nextScope cleaned entry innerOutside]
  · intro location fuel innerOutside branchOutside outerOutside
    have same : final.objects.lookup location.root = after.objects.lookup location.root := by
      change (releaseScopeState recursiveOuterActivation 0 recursiveOuterEntered.nextScope branchUnwound).objects.lookup location.root = _
      rw [releaseScopeState_root_lookup recursiveOuterActivation 0 recursiveOuterEntered.nextScope branchUnwound location.root outerOutside]
      change (releaseScopeState recursiveCheckpointTarget 1 recursiveBeforeBranch.nextScope crossed).objects.lookup location.root = _
      rw [releaseScopeState_root_lookup recursiveCheckpointTarget 1 recursiveBeforeBranch.nextScope crossed location.root branchOutside]
      change (releaseScopeState recursiveHelperActivation 0 recursiveHelperEntered.nextScope cleaned).objects.lookup location.root = _
      rw [releaseScopeState_root_lookup recursiveHelperActivation 0 recursiveHelperEntered.nextScope cleaned location.root innerOutside]
    have frame := readLoc_construction_frame fuel recursiveCheckpointConfig.layout cleaned final location same rfl
    exact (OutsideReadResult.observation _ _ _ _ frame).trans
      (readLoc_ticket_release_observation fuel recursiveCheckpointConfig.layout after 0 location)

#print axioms recursive_checkpoint_outer_handler

end Goose.Proofs.ConstructionAcceptedExecution
