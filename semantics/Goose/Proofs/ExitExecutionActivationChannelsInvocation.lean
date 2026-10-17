import Goose.Proofs.ExitExecutionActivationChannelsActivation
import Goose.Proofs.ExitExecutionActivationChannelsConstructionHelpers

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem preservesActivationChannels_callActivationTail (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (identifier : Goose.Core.ContextId)
    (implementation : Goose.Construct.Impl) (callableChannels : List Channel)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (do
      let act ← freshAct
      let activation : RuntimeActivation :=
        ⟨identifier, act, implementation.vars, [], callableChannels⟩
      let state ← EvalM.get
      EvalM.set { state with activations := activation :: state.activations }
      let carriers ← enterActivation fuel config activation pre implementation.body origin
      deliverCarriers fuel config.layout channels carriers origin) := by
  apply preservesActivationChannels_freshPushFilter
    (make := fun act => ⟨identifier, act, implementation.vars, [], callableChannels⟩)
    (identifier := by intro act; rfl)
    (enter := fun activation => enterActivation fuel config activation pre implementation.body origin)
    (continuation := fun carriers => deliverCarriers fuel config.layout channels carriers origin)
  · intro activation
    exact previous.activation activation pre implementation.body origin
  · intro activation
    exact previousFresh.activation activation pre implementation.body origin
  · intro carriers
    exact preservesActivationChannels_deliverCarriers config fuel config.layout channels carriers origin

private theorem preservesActivationChannels_callChannels (config : EvalConfig) (origin : Goose.Core.OriginId)
    (channels : List Channel) (results : List ResultDescriptor) :
    PreservesActivationChannels ((channels.zip results).mapM fun (channel, result) => do
      match result.request, channel with
      | .register, _ => pure (Channel.register result.ty)
      | .value, .construct incoming | .elementRun, .construct incoming =>
          let destination ← liftConstruction origin (renewReceivingDestination incoming)
          liftConstruction origin (adaptDestinationType destination result.ty)
          pure (.construct destination)
      | .value, .register _ | .elementRun, .register _ => fault .shape
      | _, .completion _ => fault .flow) := by
  have fresh0 := evaluationPreservesFresh_zero config
  have channels0 := evaluationActivationChannels_zero config
  apply preservesActivationChannels_listMapM
  · intro item
    rcases item with ⟨channel, result⟩
    cases request : result.request <;> cases channel <;>
      activation_channels_helper_eval_core fresh0 channels0
  · intro item
    rcases item with ⟨channel, result⟩
    cases request : result.request <;> cases channel <;> fresh_eval fresh0

private theorem preservesActivationChannels_renewCallChannels (config : EvalConfig)
    (origin : Goose.Core.OriginId) (channels : List Channel) :
    PreservesActivationChannels (channels.mapM fun channel => match channel with
      | .register ty => pure (Channel.register ty)
      | .construct destination => do
          pure (Channel.construct (← liftConstruction origin (renewReceivingDestination destination)))
      | .completion _ => fault .flow) := by
  have fresh0 := evaluationPreservesFresh_zero config
  have channels0 := evaluationActivationChannels_zero config
  activation_channels_helper_eval_core fresh0 channels0

private theorem preservesFresh_renewCallChannels (config : EvalConfig)
    (origin : Goose.Core.OriginId) (channels : List Channel) :
    PreservesFresh (channels.mapM fun channel => match channel with
      | .register ty => pure (Channel.register ty)
      | .construct destination => do
          pure (Channel.construct (← liftConstruction origin (renewReceivingDestination destination)))
      | .completion _ => fault .flow) := by
  have previous := evaluationPreservesFresh_zero config
  apply preservesFresh_listMapM
  intro channel
  cases channel <;> fresh_eval previous

theorem invokeCall_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (invokeCall (fuel + 1) config environment context arguments channels origin) := by
  simp only [invokeCall]
  apply preservesActivationChannels_bind (getImplementation config context) _
  · exact preservesActivationChannels_of_stateQuery _ (stateQuery_getImplementation config context)
  · exact stateQuery_preservesFresh _ (stateQuery_getImplementation config context)
  · intro implementationResult
    rcases implementationResult with ⟨identifier, implementation⟩
    split
    · exact preservesActivationChannels_fault _
    · apply preservesActivationChannels_bind _ _
      · exact preservesActivationChannels_callChannels config origin channels implementation.results.toList
      · apply preservesFresh_listMapM
        intro item
        rcases item with ⟨channel, result⟩
        cases request : result.request <;> cases channel <;> fresh_eval previousFresh
      · intro callableChannels
        apply preservesActivationChannels_bind
          (evalArguments fuel config environment implementation.vars implementation.params.toList arguments) _
        · exact previous.arguments _ _ _ _
        · exact previousFresh.arguments _ _ _ _
        · intro values
          apply preservesActivationChannels_bind _ _
          · exact preservesActivationChannels_renewCallChannels config origin callableChannels
          · exact preservesFresh_renewCallChannels config origin callableChannels
          · intro renewed
            apply preservesActivationChannels_bind EvalM.get _
              preservesActivationChannels_get preservesFresh_get
            intro state
            change PreservesActivationChannels
              (if state.activations.length ≥ Core.maxCallDepth then timeout else do
                let act ← freshAct
                let activation : RuntimeActivation :=
                  ⟨identifier, act, implementation.vars, [], renewed⟩
                let state ← EvalM.get
                EvalM.set { state with activations := activation :: state.activations }
                let pre := (implementation.params.toList.zip values).map
                  fun item => (item.1.var, item.2)
                let carriers ← enterActivation fuel config activation pre implementation.body origin
                deliverCarriers fuel config.layout channels carriers origin)
            apply preservesActivationChannels_conditional
            · exact preservesActivationChannels_timeout
            · exact preservesActivationChannels_callActivationTail fuel config previousFresh previous
                identifier implementation renewed
                ((implementation.params.toList.zip values).map fun item => (item.1.var, item.2))
                channels origin

end Goose.Proofs.ExitExecution
