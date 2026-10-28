import Goose.Proofs.ConstructionActivationCounterTheorem

namespace Goose.Proofs.ConstructionGhostCallHistorical
open Goose.Construct Goose.Proofs.ConstructionActivationCounter Goose.Proofs.ConstructionActivationCounterEvaluation
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostCallActivation
open Goose.Proofs.ExitExecution

theorem prepareCallableChannels_counter (environment : RuntimeActivation) (channels : List Channel)
    (implementation : Impl) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (prepareCallableChannels environment channels implementation origin) := by
  unfold prepareCallableChannels
  apply counter_listMapM
  intro item
  rcases item with ⟨channel, result⟩
  rcases result with ⟨ty, request, named⟩
  cases channel <;> cases request <;> simp only <;> repeat' first
    | exact counter_pure _
    | exact counter_stop _
    | exact counter_lift _ _
    | apply counter_bind
    | intro

theorem refreshCallableChannels_counter (channels : List Channel) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (refreshCallableChannels channels origin) := by
  unfold refreshCallableChannels
  apply counter_listMapM
  intro channel
  cases channel <;> repeat' first
    | exact counter_pure _
    | exact counter_stop _
    | exact counter_lift _ _
    | apply counter_bind
    | intro

theorem invokeCall_activation_frontier (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (before lookupReady argumentsReady valuesReady activationReady : ExecutionState)
    (id : Goose.Core.ImplId) (implementation : Impl) (callableChannels refreshed : List Channel) (values : List Value)
    (lookup : getImplementation config context before = .ok (id, implementation) lookupReady)
    (prepared : prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels argumentsReady)
    (argumentsResult : evalArguments fuel config environment implementation.vars implementation.params.toList arguments argumentsReady = .ok values valuesReady)
    (refresh : refreshCallableChannels callableChannels origin valuesReady = .ok refreshed activationReady) :
    before.nextAct ≤ activationReady.nextAct := by
  have lookupBound := counter_stateQuery _ (stateQuery_getImplementation config context) before
  simp only [lookup, Goose.Proofs.Exit.stepState] at lookupBound
  have preparationBound := prepareCallableChannels_counter environment channels implementation origin lookupReady
  simp only [prepared, Goose.Proofs.Exit.stepState] at preparationBound
  have argumentBound := (evaluation_preservesActivationCounter fuel config).arguments environment implementation.vars implementation.params.toList arguments argumentsReady
  simp only [argumentsResult, Goose.Proofs.Exit.stepState] at argumentBound
  have refreshBound := refreshCallableChannels_counter callableChannels origin valuesReady
  simp only [refresh, Goose.Proofs.Exit.stepState] at refreshBound
  exact Nat.le_trans lookupBound (Nat.le_trans preparationBound (Nat.le_trans argumentBound refreshBound))

theorem priorAllocation_beforeCallee (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (earlier before lookupReady argumentsReady valuesReady activationReady : ExecutionState)
    (earlierId : Goose.Core.ActId) (id : Goose.Core.ImplId) (implementation : Impl)
    (callableChannels refreshed : List Channel) (values : List Value)
    (earlierAllocation : freshAct earlier = .ok earlierId before)
    (lookup : getImplementation config context before = .ok (id, implementation) lookupReady)
    (prepared : prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels argumentsReady)
    (argumentsResult : evalArguments fuel config environment implementation.vars implementation.params.toList arguments argumentsReady = .ok values valuesReady)
    (refresh : refreshCallableChannels callableChannels origin valuesReady = .ok refreshed activationReady) :
    earlierId < activationReady.nextAct := by
  have exactAllocation : freshAct earlier = .ok earlier.nextAct { earlier with nextAct := earlier.nextAct + 1 } := by rfl
  have identity := ExecutionStep.ok.inj (earlierAllocation.symm.trans exactAllocation)
  have frontier := invokeCall_activation_frontier fuel config environment context arguments channels origin
    before lookupReady argumentsReady valuesReady activationReady id implementation callableChannels refreshed values
    lookup prepared argumentsResult refresh
  rw [identity.2] at frontier
  rw [identity.1]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) frontier

theorem priorAllocation_beforeCallee_acrossCall (fuel priorFuel : Nat) (config : EvalConfig)
    (environment priorEnvironment : RuntimeActivation) (context priorContext : Goose.Core.ContextId)
    (arguments priorArguments : List Arg) (channels priorChannels : List Channel) (origin priorOrigin : Goose.Core.OriginId)
    (earlier firstReady before lookupReady argumentsReady valuesReady activationReady : ExecutionState)
    (earlierId : Goose.Core.ActId) (id : Goose.Core.ImplId) (implementation : Impl)
    (callableChannels refreshed : List Channel) (values : List Value) (priorCarriers : List Carrier)
    (earlierAllocation : freshAct earlier = .ok earlierId firstReady)
    (priorCall : invokeCall priorFuel config priorEnvironment priorContext priorArguments priorChannels priorOrigin firstReady =
      .ok priorCarriers before)
    (lookup : getImplementation config context before = .ok (id, implementation) lookupReady)
    (prepared : prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels argumentsReady)
    (argumentsResult : evalArguments fuel config environment implementation.vars implementation.params.toList arguments argumentsReady = .ok values valuesReady)
    (refresh : refreshCallableChannels callableChannels origin valuesReady = .ok refreshed activationReady) :
    earlierId < activationReady.nextAct := by
  have exactAllocation : freshAct earlier = .ok earlier.nextAct { earlier with nextAct := earlier.nextAct + 1 } := by rfl
  have identity := ExecutionStep.ok.inj (earlierAllocation.symm.trans exactAllocation)
  have previousBound := (evaluation_preservesActivationCounter priorFuel config).call priorEnvironment priorContext
    priorArguments priorChannels priorOrigin firstReady
  simp only [priorCall, Goose.Proofs.Exit.stepState] at previousBound
  have frontier := invokeCall_activation_frontier fuel config environment context arguments channels origin
    before lookupReady argumentsReady valuesReady activationReady id implementation callableChannels refreshed values
    lookup prepared argumentsResult refresh
  rw [identity.2] at previousBound
  rw [identity.1]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_trans previousBound frontier)

#print axioms priorAllocation_beforeCallee_acrossCall
#print axioms invokeCall_activation_frontier
#print axioms priorAllocation_beforeCallee
end Goose.Proofs.ConstructionGhostCallHistorical
