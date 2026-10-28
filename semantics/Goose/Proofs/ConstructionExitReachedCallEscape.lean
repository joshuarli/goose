import Goose.Proofs.ConstructionExitCheckpointEntryTrace

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId ContextId ImplId)
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ExitExecution
open Goose.Proofs.ExitExecutionChecks

theorem recursive_branch_reaches_call_value {rootFuel : Nat}
    (reached : ExitReached rootFuel recursiveCheckpointConfig
      (.statement 13 recursiveCheckpointTarget
        (.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0)) recursiveBeforeBranch) :
    ExitReached rootFuel recursiveCheckpointConfig
      (.value 9 recursiveCallerScope (.call 2 [] 0)) recursiveBeforeHelper := by
  have condition : ((do expectBool (← evalValue 12 recursiveCheckpointConfig recursiveCheckpointTarget recursiveBranchCondition)) : EvalM Bool)
      recursiveBeforeBranch = .ok true recursiveBeforeBranch := by cbv
  have block : ExitReached rootFuel recursiveCheckpointConfig
      (.block 12 recursiveCheckpointTarget [] [] recursiveBranchBlock) recursiveBeforeBranch :=
    .call reached (.statements (.ifYes 12 recursiveCheckpointTarget recursiveBranchCondition recursiveBranchBlock
      (some recursiveOuterElse) 0 recursiveBeforeBranch recursiveBeforeBranch condition))
  have binding : bindAll recursiveCheckpointTarget.act recursiveBeforeBranch.nextScope []
      { recursiveBeforeBranch with nextScope := recursiveBeforeBranch.nextScope + 1 } = .ok () recursiveBeforeHelper := by cbv
  have environment : { recursiveCheckpointTarget with scopes :=
      (1, recursiveBeforeBranch.nextScope) :: recursiveCheckpointTarget.scopes } = recursiveCallerScope := by cbv
  have statements : ExitReached rootFuel recursiveCheckpointConfig
      (.statements 11 recursiveCallerScope [.expr (.call 2 [] 0) 0]) recursiveBeforeHelper := by
    have edge := ExitCallSite.blockStatements (config := recursiveCheckpointConfig) 11 recursiveCheckpointTarget [] [] 1
      [.expr (.call 2 [] 0) 0] none recursiveBeforeBranch recursiveBeforeHelper binding
    rw [environment] at edge
    exact .call block (by simpa [recursiveBranchBlock] using edge)
  have statement : ExitReached rootFuel recursiveCheckpointConfig
      (.statement 10 recursiveCallerScope (.expr (.call 2 [] 0) 0)) recursiveBeforeHelper :=
    .call statements (.statementsHead 10 recursiveCallerScope (.expr (.call 2 [] 0) 0) [] recursiveBeforeHelper)
  have value : ExitReached rootFuel recursiveCheckpointConfig
      (.value 9 recursiveCallerScope (.call 2 [] 0)) recursiveBeforeHelper :=
    .call statement (.statements (.expression 9 recursiveCallerScope (.call 2 [] 0) 0 recursiveBeforeHelper))
  exact value

theorem recursive_outer_reaches_call_value {rootFuel : Nat}
    (reached : ExitReached rootFuel recursiveCheckpointConfig
      (.activation 16 recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody 0) recursiveOuterEntered) :
    ExitReached rootFuel recursiveCheckpointConfig
      (.value 9 recursiveCallerScope (.call 2 [] 0)) recursiveBeforeHelper := by
  have implementation : recursiveCheckpointConfig.module.impls[recursiveOuterActivation.implementation]? =
      some ⟨"builder", #[⟨0, .byValue⟩], #[⟨array, .value, none⟩], recursiveOuterActivation.vars, recursiveOuterBody,
        .known ⟨[], [], [], [], [], [0], [], [], true, true⟩⟩ := by cbv
  have body : ExitReached rootFuel recursiveCheckpointConfig
      (.activationBody 15 recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody) recursiveOuterEntered :=
    .call reached (.activationBody 15 recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody 0 recursiveOuterEntered _ implementation)
  have scope : ExitReached rootFuel recursiveCheckpointConfig
      (.activationScope 14 recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody) recursiveOuterEntered :=
    .call body (.activationScope 14 recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody recursiveOuterEntered)
  have binding : bindAll recursiveOuterActivation.act recursiveOuterEntered.nextScope [(0, .int .i64 0)] { recursiveOuterEntered with
      nextScope := recursiveOuterEntered.nextScope + 1
      activations := recursiveOuterEntered.activations.map (fun current => if current.act == recursiveOuterActivation.act then
        { current with scopes := (0, recursiveOuterEntered.nextScope) :: recursiveOuterActivation.scopes } else current) } =
      .ok () recursiveBeforeBranch := by cbv
  have environment : { recursiveOuterActivation with scopes :=
      (0, recursiveOuterEntered.nextScope) :: recursiveOuterActivation.scopes } = recursiveCheckpointTarget := by cbv
  have statements : ExitReached rootFuel recursiveCheckpointConfig
      (.statements 14 recursiveCheckpointTarget [.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0])
      recursiveBeforeBranch := by
    have edge := ExitCallSite.activationStatements (config := recursiveCheckpointConfig) 14 recursiveOuterActivation
      [(0, .int .i64 0)] 0 [.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0] none
      recursiveOuterEntered recursiveBeforeBranch binding
    rw [environment] at edge
    exact .call scope (by simpa [recursiveOuterBody] using edge)
  have branch : ExitReached rootFuel recursiveCheckpointConfig
      (.statement 13 recursiveCheckpointTarget (.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0))
      recursiveBeforeBranch :=
    .call statements (.statementsHead 13 recursiveCheckpointTarget _ [] recursiveBeforeBranch)
  exact recursive_branch_reaches_call_value branch

theorem reached_call_value_escape_history {rootFuel fuel : Nat} (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (context : ContextId) (arguments : List Arg) (origin : OriginId)
    (initial lookupState prepared entered final : ExecutionState) (implementationId : ImplId) (implementation : Impl)
    (channels : List Channel) (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (address : ExitAddress) (carriers : List Carrier) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized initial ambient types live regions pending)
    (history : EvaluationHistoryCoverage initial ambient pending)
    (reached : ExitReached rootFuel config (.value (fuel + 2) environment (.call context arguments origin)) initial)
    (lookup : getImplementation config context initial = .ok (implementationId, implementation) lookupState)
    (receiving : channelsFor config.layout environment.act implementation.results.toList origin lookupState = .ok channels prepared)
    (callPrefix : CallActivationPrefix fuel config environment context arguments channels origin prepared activation pre body entered)
    (escaped : enterActivation fuel config activation pre body origin entered = .escape address carriers final) :
    ExitReached rootFuel config (.activation fuel activation pre body origin) entered ∧
    evalValue (fuel + 2) config environment (.call context arguments origin) initial = .escape address carriers final ∧
    EvaluationHistoryLifecycle final (.returned carriers :: ambient) (⟨channels, carriers⟩ :: pending) := by
  have call : ExitReached rootFuel config (.call (fuel + 1) environment context arguments channels origin) prepared :=
    .call reached (.values (.valueCall lookup receiving))
  have child : ExitReached rootFuel config (.activation fuel activation pre body origin) entered :=
    .call call (.callActivation fuel environment context arguments channels origin prepared entered activation pre body callPrefix)
  have callEscaped := callPrefix.escape_call address carriers escaped
  have valueEscaped : evalValue (fuel + 2) config environment (.call context arguments origin) initial =
      .escape address carriers final := by
    simp only [evalValue, bind, lookup, receiving, callEscaped]
  have tracked := evaluator_history_outcome (fuel + 2) config .none _ (.value environment (.call context arguments origin))
    initial ambient pending channels ⟨world.ownership.source.structural.1.1, history⟩
  refine ⟨child, valueEscaped, ?_⟩
  simpa only [valueEscaped, EvaluationHistoryLifecycleOutcome] using tracked

#print axioms reached_call_value_escape_history

theorem recursive_reached_call_escapes_to_handler :
    validate recursiveDestinations = .ok () ∧
    runModule 32 recursiveCheckpointConfig .initial = .ok () recursiveFullFinal ∧
    ExitReached 32 recursiveCheckpointConfig (.value 9 recursiveCallerScope (.call 2 [] 0)) recursiveBeforeHelper ∧
    ∃ built final : ExecutionState,
      let cleaned := { built with construction := { built.construction with
        exitReservations := built.construction.exitReservations.set! 0 .released } }
      let unwound := releaseScopeState recursiveHelperActivation 0 recursiveHelperEntered.nextScope cleaned
      let crossed := { unwound with activations := unwound.activations.filter (fun current => current.act != recursiveHelperActivation.act) }
      evalValue 9 recursiveCheckpointConfig recursiveCallerScope (.call 2 [] 0) recursiveBeforeHelper =
        .escape ⟨2, .nonlocal 0⟩ [.completed 1] crossed ∧
      LandedResultChannels crossed [.construct 1] [.varr (.int .u8)] [.completed 1] ∧
      enterActivation 16 recursiveCheckpointConfig recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody 0 recursiveOuterEntered =
        .ok [.completed 1] final := by
  obtain ⟨built, call, landed, _⟩ := recursive_checkpoint_helper_call_escape
  obtain ⟨_, final, handler, _⟩ := recursive_checkpoint_outer_handler
  have lookup : getImplementation recursiveCheckpointConfig 2 recursiveBeforeHelper = .ok (2, recursiveHelper) recursiveBeforeHelper := by cbv
  have channels : channelsFor recursiveCheckpointConfig.layout recursiveCallerScope.act recursiveHelper.results.toList 0 recursiveBeforeHelper =
      .ok [] recursiveBeforeHelper := by cbv
  refine ⟨validated_recursive_direct_return.1, recursive_successful_run_execution.1,
    recursive_outer_reaches_call_value recursive_outer_activation_reached, built, final, ?_, ?_, handler⟩
  · simp only [evalValue, bind, lookup, channels, call]
  · let cleaned := { built with construction := { built.construction with
      exitReservations := built.construction.exitReservations.set! 0 .released } }
    let unwound := releaseScopeState recursiveHelperActivation 0 recursiveHelperEntered.nextScope cleaned
    let crossed := { unwound with activations := unwound.activations.filter (fun current => current.act != recursiveHelperActivation.act) }
    exact LandedResultChannels.of_construction_eq (before := cleaned) (after := crossed) rfl landed

#print axioms recursive_reached_call_escapes_to_handler
#print axioms recursive_outer_reaches_call_value
#print axioms recursive_branch_reaches_call_value

end Goose.Proofs.ConstructionAcceptedExecution
