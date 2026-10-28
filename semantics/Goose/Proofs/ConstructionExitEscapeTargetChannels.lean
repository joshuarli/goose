import Goose.Proofs.ConstructionExitReachedCallEscape

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId ContextId ImplId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution
open Goose.Proofs.ExitExecutionChecks

theorem returned_history_rechannel (state : ExecutionState) (ambient : OwnershipAmbient)
    (pending : List PendingCarrierFrame) (oldChannels newChannels : List Channel) (carriers : List Carrier)
    (valid : EvaluationHistoryLifecycle state (.returned carriers :: ambient)
      (⟨oldChannels, carriers⟩ :: pending)) :
    EvaluationHistoryLifecycle state (.returned carriers :: ambient)
      (⟨newChannels, carriers⟩ :: pending) := by
  refine ⟨valid.1, valid.2.1, ?_⟩
  intro id member
  obtain ⟨frame, present, retained⟩ := valid.2.2 id member
  rcases List.mem_cons.mp present with equal | prior
  · subst frame
    exact ⟨⟨newChannels, carriers⟩, by simp, retained⟩
  · exact ⟨frame, List.mem_cons_of_mem _ prior, retained⟩

theorem reached_call_target_escape_history {rootFuel fuel : Nat} (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (context : ContextId) (arguments : List Arg) (origin : OriginId)
    (initial lookupState prepared entered final : ExecutionState) (implementationId : ImplId) (implementation : Impl)
    (channels : List Channel) (activation target : RuntimeActivation) (targetId : Nat)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) (carriers : List Carrier) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized initial ambient types live regions pending)
    (history : EvaluationHistoryCoverage initial ambient pending)
    (reached : ExitReached rootFuel config (.value (fuel + 2) environment (.call context arguments origin)) initial)
    (lookup : getImplementation config context initial = .ok (implementationId, implementation) lookupState)
    (receiving : channelsFor config.layout environment.act implementation.results.toList origin lookupState = .ok channels prepared)
    (selected : targetActivation config targetId initial = .ok target initial)
    (callPrefix : CallActivationPrefix fuel config environment context arguments channels origin prepared activation pre body entered)
    (escaped : enterActivation fuel config activation pre body origin entered =
      .escape ⟨target.act, .nonlocal targetId⟩ carriers final) :
    ExitReached rootFuel config (.activation fuel activation pre body origin) entered ∧
    evalValue (fuel + 2) config environment (.call context arguments origin) initial =
      .escape ⟨target.act, .nonlocal targetId⟩ carriers final ∧
    EvaluationHistoryLifecycle final (.returned carriers :: ambient) (⟨target.channels, carriers⟩ :: pending) := by
  obtain ⟨child, propagated, tracked⟩ := reached_call_value_escape_history config initialized environment context arguments origin
    initial lookupState prepared entered final implementationId implementation channels activation pre body
    ⟨target.act, .nonlocal targetId⟩ carriers ambient types live regions pending world history reached lookup receiving callPrefix escaped
  exact ⟨child, propagated, returned_history_rechannel final ambient pending channels target.channels carriers tracked⟩

theorem recursive_escape_uses_target_channels :
    validate recursiveDestinations = .ok () ∧
    runModule 32 recursiveCheckpointConfig .initial = .ok () recursiveFullFinal ∧
    ExitReached 32 recursiveCheckpointConfig (.value 9 recursiveCallerScope (.call 2 [] 0)) recursiveBeforeHelper ∧
    channelsFor recursiveCheckpointConfig.layout recursiveCallerScope.act recursiveHelper.results.toList 0 recursiveBeforeHelper =
      .ok [] recursiveBeforeHelper ∧
    targetActivation recursiveCheckpointConfig 0 recursiveBeforeHelper = .ok recursiveCheckpointTarget recursiveBeforeHelper ∧
    recursiveCheckpointTarget.channels = [.construct 1] ∧
    ∃ built final : ExecutionState,
      let cleaned := { built with construction := { built.construction with
        exitReservations := built.construction.exitReservations.set! 0 .released } }
      let unwound := releaseScopeState recursiveHelperActivation 0 recursiveHelperEntered.nextScope cleaned
      let crossed := { unwound with activations := unwound.activations.filter (fun current => current.act != recursiveHelperActivation.act) }
      evalValue 9 recursiveCheckpointConfig recursiveCallerScope (.call 2 [] 0) recursiveBeforeHelper =
        .escape ⟨2, .nonlocal 0⟩ [.completed 1] crossed ∧
      ¬ CarriersLandingReady crossed [] [.completed 1] ∧
      LandedResultChannels crossed recursiveCheckpointTarget.channels [.varr (.int .u8)] [.completed 1] ∧
      enterActivation 16 recursiveCheckpointConfig recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody 0 recursiveOuterEntered =
        .ok [.completed 1] final := by
  obtain ⟨validated, executed, reached, built, final, escaped, landed, handled⟩ := recursive_reached_call_escapes_to_handler
  have callChannels : channelsFor recursiveCheckpointConfig.layout recursiveCallerScope.act recursiveHelper.results.toList 0 recursiveBeforeHelper =
      .ok [] recursiveBeforeHelper := by cbv
  have target : targetActivation recursiveCheckpointConfig 0 recursiveBeforeHelper = .ok recursiveCheckpointTarget recursiveBeforeHelper := by cbv
  refine ⟨validated, executed, reached, callChannels, target, rfl, built, final, escaped, ?_, ?_, handled⟩
  · intro impossible
    have lengths := impossible.lengths
    simp at lengths
  · simpa only [recursiveCheckpointTarget] using landed

#print axioms returned_history_rechannel
#print axioms reached_call_target_escape_history
#print axioms recursive_escape_uses_target_channels

end Goose.Proofs.ConstructionAcceptedExecution
