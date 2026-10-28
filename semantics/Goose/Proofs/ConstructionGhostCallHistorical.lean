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

theorem invokeCall_activation_bounds (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (before lookupReady argumentsReady valuesReady activationReady : ExecutionState)
    (id : Goose.Core.ImplId) (implementation : Impl) (callableChannels refreshed : List Channel) (values : List Value)
    (lookup : getImplementation config context before = .ok (id, implementation) lookupReady)
    (arity : channels.length = implementation.results.size)
    (prepared : prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels argumentsReady)
    (argumentsResult : evalArguments fuel config environment implementation.vars implementation.params.toList arguments argumentsReady = .ok values valuesReady)
    (refresh : refreshCallableChannels callableChannels origin valuesReady = .ok refreshed activationReady)
    (depth : activationReady.activations.length < Goose.Core.maxCallDepth) :
    before.nextAct ≤ activationReady.nextAct ∧
      activationReady.nextAct < (Goose.Proofs.Exit.stepState
        (invokeCall (fuel + 1) config environment context arguments channels origin before)).nextAct := by
  refine ⟨invokeCall_activation_frontier fuel config environment context arguments channels origin before lookupReady
    argumentsReady valuesReady activationReady id implementation callableChannels refreshed values lookup prepared argumentsResult refresh, ?_⟩
  obtain ⟨outcome, visits, replay, ordered, once, execution⟩ :=
    invokeCall_argumentReplay fuel config environment context arguments channels origin before lookupReady argumentsReady
      id implementation callableChannels lookup arity prepared
  have actual := replay.sound
  rw [argumentsResult] at actual
  subst outcome
  let activation : RuntimeActivation := ⟨id, activationReady.nextAct, implementation.vars, [], refreshed⟩
  let activated := { activationReady with nextAct := activationReady.nextAct + 1, activations := activation :: activationReady.activations }
  have continuation : PreservesActivationCounter (enterActivation fuel config activation
      ((implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value))
      implementation.body origin >>= fun carriers => deliverCarriers fuel config.layout channels carriers origin) := by
    apply counter_bind
    · exact (evaluation_preservesActivationCounter fuel config).activation _ _ _ _
    · intro carriers
      exact counter_deliverCarriers _ _ _ _ _
  have lower := continuation activated
  rw [execution]
  have entered := callAfterArguments_activation fuel config id implementation channels callableChannels refreshed origin values
    valuesReady activationReady refresh depth
  dsimp only [callArgumentsContinuation] at *
  rw [entered]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) lower

#print axioms invokeCall_activation_bounds
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

def CompletedCallAllocation (config : EvalConfig) (before after : ExecutionState) (activationId : Goose.Core.ActId) : Prop :=
  ∃ fuel environment context arguments channels origin lookupReady argumentsReady valuesReady activationReady
      id implementation callableChannels refreshed values carriers,
    getImplementation config context before = .ok (id, implementation) lookupReady ∧
    channels.length = implementation.results.size ∧
    prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels argumentsReady ∧
    evalArguments fuel config environment implementation.vars implementation.params.toList arguments argumentsReady = .ok values valuesReady ∧
    refreshCallableChannels callableChannels origin valuesReady = .ok refreshed activationReady ∧
    activationReady.activations.length < Goose.Core.maxCallDepth ∧
    activationId = activationReady.nextAct ∧
    invokeCall (fuel + 1) config environment context arguments channels origin before = .ok carriers after

theorem completedCallAllocation_bounds {config : EvalConfig} {before after : ExecutionState}
    {activationId : Goose.Core.ActId} (call : CompletedCallAllocation config before after activationId) :
    before.nextAct ≤ activationId ∧ activationId < after.nextAct := by
  obtain ⟨fuel, environment, context, arguments, channels, origin, lookupReady, argumentsReady, valuesReady,
    activationReady, id, implementation, callableChannels, refreshed, values, carriers, lookup, arity, prepared,
    argumentsResult, refresh, depth, identity, completed⟩ := call
  have bounds := invokeCall_activation_bounds fuel config environment context arguments channels origin before lookupReady
    argumentsReady valuesReady activationReady id implementation callableChannels refreshed values
    lookup arity prepared argumentsResult refresh depth
  simpa only [identity, completed, Goose.Proofs.Exit.stepState] using bounds

inductive CompletedCallHistory (config : EvalConfig) : ExecutionState → ExecutionState → List Goose.Core.ActId → Prop
  | done (state : ExecutionState) : CompletedCallHistory config state state []
  | next {before middle after : ExecutionState} {activationId : Goose.Core.ActId} {ids : List Goose.Core.ActId}
      (call : CompletedCallAllocation config before middle activationId)
      (remaining : CompletedCallHistory config middle after ids) :
      CompletedCallHistory config before after (activationId :: ids)

theorem CompletedCallHistory.bounds
    (history : CompletedCallHistory config before after ids) :
    before.nextAct ≤ after.nextAct ∧
      ∀ id ∈ ids, before.nextAct ≤ id ∧ id < after.nextAct := by
  induction history with
  | done state => simp
  | next call remaining ih =>
    obtain ⟨firstLower, firstUpper⟩ := completedCallAllocation_bounds call
    have beforeMiddle := Nat.le_trans firstLower (Nat.le_of_lt firstUpper)
    refine ⟨Nat.le_trans beforeMiddle ih.1, ?_⟩
    intro id member
    simp only [List.mem_cons] at member
    rcases member with same | later
    · subst id
      exact ⟨firstLower, Nat.lt_of_lt_of_le firstUpper ih.1⟩
    · obtain ⟨lower, upper⟩ := ih.2 id later
      exact ⟨Nat.le_trans beforeMiddle lower, upper⟩

theorem CompletedCallHistory.unique (history : CompletedCallHistory config before after ids) : ids.Nodup := by
  induction history with
  | done => exact List.nodup_nil
  | next call remaining ih =>
    simp only [List.nodup_cons]
    constructor
    · intro member
      have lower := (remaining.bounds).2 _ member
      have lowerBound := lower.1
      have upper := (completedCallAllocation_bounds call).2
      exact (Nat.not_le_of_gt upper) lowerBound
    · exact ih

private def witnessImplementation : Impl :=
  ⟨"callee", #[], #[], #[], .mk 0 [.print [.text "called"] 0] none, .unknown⟩
private def witnessConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[witnessImplementation], #[⟨0, "callee", [], [], []⟩], 0, #[], #[], #[]⟩⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def witnessState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem completedCallAllocation_witness :
    ∃ after, CompletedCallAllocation witnessConfig .initial after 0 ∧
      after.construction.stdout.data.toList = [99, 97, 108, 108, 101, 100, 10] := by
  let after := witnessState (invokeCall 21 witnessConfig witnessEnvironment 0 [] [] 0 .initial)
  refine ⟨after, ?_, ?_⟩
  · refine ⟨20, witnessEnvironment, 0, [], [], 0, .initial, .initial, .initial, .initial,
      0, witnessImplementation, [], [], [], [], ?_⟩
    unfold after witnessConfig witnessImplementation witnessEnvironment witnessState
    cbv
  · unfold after witnessConfig witnessImplementation witnessEnvironment witnessState
    cbv

#print axioms completedCallAllocation_witness
#print axioms completedCallAllocation_bounds
#print axioms CompletedCallHistory.unique
#print axioms priorAllocation_beforeCallee_acrossCall
#print axioms invokeCall_activation_frontier
#print axioms priorAllocation_beforeCallee
end Goose.Proofs.ConstructionGhostCallHistorical
