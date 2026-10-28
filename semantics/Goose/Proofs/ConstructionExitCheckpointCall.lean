import Goose.Proofs.ConstructionExitCheckpointReturn
import Goose.Proofs.ExitExecutionInvocation
import Goose.Proofs.ExitExecutionPathDispatchUnwind

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ExitExecution
open Goose.Proofs.ExitExecutionChecks

def recursiveBeforeHelper : ExecutionState :=
  Goose.Proofs.Exit.stepState (runModule 25 recursiveCheckpointConfig .initial)

def recursiveHelperEntered : ExecutionState :=
  Goose.Proofs.Exit.stepState (runModule 26 recursiveCheckpointConfig .initial)

def recursiveHelper : Impl :=
  ⟨"helper", #[], #[], #[], .mk 0 [.returnFrom 0 [.bytes array [66] 0] 0] none,
    .known ⟨[], [], [], [], [], [], [0], [0], false, false⟩⟩

def recursiveHelperActivation : RuntimeActivation := ⟨2, 3, #[], [], []⟩

def recursiveCallerScope : RuntimeActivation :=
  { recursiveCheckpointTarget with scopes := (1, 4) :: recursiveCheckpointTarget.scopes }

theorem recursive_checkpoint_call_prefix (fuel : Nat) :
    CallActivationPrefix (fuel + 1) recursiveCheckpointConfig recursiveCallerScope 2 [] [] 0
      recursiveBeforeHelper recursiveHelperActivation [] recursiveHelper.body recursiveHelperEntered := by
  have lookup : getImplementation recursiveCheckpointConfig 2 recursiveBeforeHelper =
      .ok (2, recursiveHelper) recursiveBeforeHelper := by cbv
  have arguments : evalArguments (fuel + 1) recursiveCheckpointConfig recursiveCallerScope #[] [] []
      recursiveBeforeHelper = .ok [] recursiveBeforeHelper := by
    simp [evalArguments, pure]
  have depth : recursiveBeforeHelper.activations.length < Goose.Core.maxCallDepth := by cbv
  have receiving : CallArgumentPrefix recursiveCheckpointConfig 2 [] 0 recursiveBeforeHelper
      2 recursiveHelper [] recursiveBeforeHelper := by
    exact .actual recursiveBeforeHelper recursiveBeforeHelper recursiveBeforeHelper 2 recursiveHelper [] lookup rfl rfl
  have prepared := CallActivationPrefix.actual recursiveBeforeHelper recursiveBeforeHelper recursiveBeforeHelper
    recursiveBeforeHelper 2 recursiveHelper [] [] [] receiving arguments rfl depth
  have entered : { recursiveBeforeHelper with
      nextAct := recursiveBeforeHelper.nextAct + 1
      activations := ⟨2, recursiveBeforeHelper.nextAct, recursiveHelper.vars, [], []⟩ :: recursiveBeforeHelper.activations } =
      recursiveHelperEntered := by cbv
  have activation : (⟨2, recursiveBeforeHelper.nextAct, recursiveHelper.vars, [], []⟩ : RuntimeActivation) = recursiveHelperActivation := by cbv
  rw [entered, activation] at prepared
  simpa [recursiveHelper] using prepared

theorem recursive_checkpoint_helper_binding :
    bindAll recursiveHelperActivation.act recursiveHelperEntered.nextScope [] { recursiveHelperEntered with
      nextScope := recursiveHelperEntered.nextScope + 1
      activations := recursiveHelperEntered.activations.map (fun current => if current.act == recursiveHelperActivation.act then
        { current with scopes := (0, recursiveHelperEntered.nextScope) :: recursiveHelperActivation.scopes } else current) } =
      .ok () recursiveDirectCheckpoint := by cbv

theorem recursive_checkpoint_helper_call_escape :
    ∃ after : ExecutionState,
      let cleaned := { after with construction := { after.construction with
        exitReservations := after.construction.exitReservations.set! 0 .released } }
      let unwound := releaseScopeState recursiveHelperActivation 0 recursiveHelperEntered.nextScope cleaned
      invokeCall 8 recursiveCheckpointConfig recursiveCallerScope 2 [] [] 0 recursiveBeforeHelper =
        .escape ⟨2, .nonlocal 0⟩ [.completed 1]
          { unwound with activations := unwound.activations.filter (fun current => current.act != recursiveHelperActivation.act) } ∧
      LandedResultChannels cleaned [.construct 1] [.varr (.int .u8)] [.completed 1] ∧
      RecursiveCheckpointOutsideFrame after := by
  obtain ⟨after, returned, finished, landed, outsideFrame⟩ := recursive_checkpoint_direct_return
  let cleaned := { after with construction := { after.construction with
    exitReservations := after.construction.exitReservations.set! 0 .released } }
  let unwound := releaseScopeState recursiveHelperActivation 0 recursiveHelperEntered.nextScope cleaned
  have environmentEq : { recursiveHelperActivation with scopes := (0, recursiveHelperEntered.nextScope) :: recursiveHelperActivation.scopes } =
      recursiveCheckpointSource := by cbv
  have statements : execStmts 5 recursiveCheckpointConfig recursiveCheckpointSource
      [.returnFrom 0 [.bytes array [66] 0] 0] recursiveDirectCheckpoint =
      .escape ⟨2, .nonlocal 0⟩ [.completed 1] cleaned := by
    simp only [array, execStmts, bind, returned]
    rfl
  have body : execActivationBody 6 recursiveCheckpointConfig recursiveHelperActivation [] recursiveHelper.body recursiveHelperEntered =
      .escape ⟨2, .nonlocal 0⟩ [.completed 1] unwound := by
    unfold execActivationBody execResultScope
    have fresh : freshScope = fun state => .ok state.nextScope { state with nextScope := state.nextScope + 1 } := by
      funext state
      rfl
    rw [fresh]
    simp only [bind, EvalM.get, EvalM.set, withScope, recursive_checkpoint_helper_binding, recursiveHelper]
    rw [environmentEq]
    simp only [statements, releaseScope, bind, EvalM.get, EvalM.set]
    rfl
  have lookup : recursiveCheckpointConfig.module.impls[recursiveHelperActivation.implementation]? = some recursiveHelper := by cbv
  have escaped : enterActivation 7 recursiveCheckpointConfig recursiveHelperActivation [] recursiveHelper.body 0 recursiveHelperEntered =
      .escape ⟨2, .nonlocal 0⟩ [.completed 1]
        { unwound with activations := unwound.activations.filter (fun current => current.act != recursiveHelperActivation.act) } := by
    simp only [enterActivation, lookup]
    exact Goose.Proofs.Exit.runtime_activation_propagates recursiveCheckpointConfig.layout recursiveHelperActivation
      (recursiveHelper.results.toList.map (·.ty)) 0 _ recursiveHelperEntered unwound ⟨2, .nonlocal 0⟩ [.completed 1] body (by decide)
  exact ⟨after, (recursive_checkpoint_call_prefix 6).escape_call _ _ escaped, landed, outsideFrame⟩

#print axioms recursive_checkpoint_helper_call_escape
#print axioms recursive_checkpoint_call_prefix
#print axioms recursive_checkpoint_helper_binding

end Goose.Proofs.ConstructionAcceptedExecution
