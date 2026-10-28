import Goose.Proofs.ConstructionGhostCallArguments
import Goose.Proofs.ExitExecution

namespace Goose.Proofs.ConstructionGhostCallActivation
open Goose.Construct Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostArguments Goose.Proofs.ExitExecution

def refreshCallableChannels (channels : List Channel) (origin : Goose.Core.OriginId) : EvalM (List Channel) :=
  channels.mapM fun channel => match channel with
    | .register ty => pure (.register ty)
    | .construct destination => do
        pure (.construct (← liftConstruction origin (renewReceivingDestination destination)))
    | .completion _ => fault .flow

theorem callAfterArguments_activation (fuel : Nat) (config : EvalConfig) (id : Goose.Core.ImplId)
    (implementation : Impl) (channels callableChannels refreshed : List Channel) (origin : Goose.Core.OriginId)
    (values : List Value) (before ready : ExecutionState)
    (refresh : refreshCallableChannels callableChannels origin before = .ok refreshed ready)
    (depth : ready.activations.length < Goose.Core.maxCallDepth) :
    let activation : RuntimeActivation := ⟨id, ready.nextAct, implementation.vars, [], refreshed⟩
    let activated := { ready with nextAct := ready.nextAct + 1, activations := activation :: ready.activations }
    callAfterArguments fuel config id implementation channels callableChannels origin values before =
      (enterActivation fuel config activation
        ((implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value))
        implementation.body origin >>= fun carriers => deliverCarriers fuel config.layout channels carriers origin) activated := by
  dsimp only
  change (refreshCallableChannels callableChannels origin >>= fun selected => do
    let state ← EvalM.get
    if state.activations.length ≥ Goose.Core.maxCallDepth then timeout
    let act ← freshAct
    let activation : RuntimeActivation := ⟨id, act, implementation.vars, [], selected⟩
    let state ← EvalM.get
    EvalM.set { state with activations := activation :: state.activations }
    let pre := (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
    let carriers ← enterActivation fuel config activation pre implementation.body origin
    deliverCarriers fuel config.layout channels carriers origin) before = _
  simp only [bind, refresh, EvalM.get, EvalM.set, freshAct, pure, Nat.not_le.mpr depth, ↓reduceIte]

theorem newActivation_distinctFromActive (ready : ExecutionState) (fresh : FreshActivations ready)
    (current : RuntimeActivation) (member : current ∈ ready.activations) : current.act ≠ ready.nextAct :=
  Nat.ne_of_lt (fresh.2 current member)

theorem invokeCall_argumentActivation (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (before lookupReady argumentsReady valuesReady activationReady : ExecutionState)
    (id : Goose.Core.ImplId) (implementation : Impl) (callableChannels refreshed : List Channel) (values : List Value)
    (lookup : getImplementation config context before = .ok (id, implementation) lookupReady)
    (arity : channels.length = implementation.results.size)
    (prepared : prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels argumentsReady)
    (argumentsResult : evalArguments fuel config environment implementation.vars implementation.params.toList arguments argumentsReady = .ok values valuesReady)
    (refresh : refreshCallableChannels callableChannels origin valuesReady = .ok refreshed activationReady)
    (depth : activationReady.activations.length < Goose.Core.maxCallDepth) (fresh : FreshActivations activationReady) :
    let activation : RuntimeActivation := ⟨id, activationReady.nextAct, implementation.vars, [], refreshed⟩
    let activated := { activationReady with nextAct := activationReady.nextAct + 1, activations := activation :: activationReady.activations }
    ∃ visits,
      ArgumentReplay config environment implementation.vars fuel 0 implementation.params.toList arguments argumentsReady
        (.ok values valuesReady) visits ∧
      visits.map ArgumentInvocation.argument = arguments.take visits.length ∧
      (visits.map ArgumentInvocation.ordinal).Nodup ∧
      (∀ current ∈ activationReady.activations, current.act ≠ activation.act) ∧
      invokeCall (fuel + 1) config environment context arguments channels origin before =
        (enterActivation fuel config activation
          ((implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value))
          implementation.body origin >>= fun carriers => deliverCarriers fuel config.layout channels carriers origin) activated := by
  obtain ⟨outcome, visits, replay, ordered, once, execution⟩ :=
    invokeCall_argumentReplay fuel config environment context arguments channels origin before lookupReady argumentsReady
      id implementation callableChannels lookup arity prepared
  have actual := replay.sound
  rw [argumentsResult] at actual
  subst outcome
  refine ⟨visits, replay, ordered, once, ?_, ?_⟩
  · intro current member
    exact newActivation_distinctFromActive activationReady fresh current member
  · rw [execution]
    exact callAfterArguments_activation fuel config id implementation channels callableChannels refreshed origin values
      valuesReady activationReady refresh depth

#print axioms invokeCall_argumentActivation
#print axioms callAfterArguments_activation
#print axioms newActivation_distinctFromActive
end Goose.Proofs.ConstructionGhostCallActivation
