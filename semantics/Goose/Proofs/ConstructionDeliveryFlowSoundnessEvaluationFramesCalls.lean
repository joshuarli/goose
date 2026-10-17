import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationFramesProducers

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem evalArguments_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameters : List Param) (arguments : List Arg) :
    BreakFrameAction (evalArguments (fuel + 1) config environment vars parameters arguments) := by
  cases parameters with
  | nil =>
      cases arguments <;> simp only [evalArguments]
      · exact breakFrame_pure _
      · exact breakFrame_stop _
  | cons parameter parameters =>
      cases arguments with
      | nil => simpa only [evalArguments, fault] using breakFrame_stop (Goose.Core.Stop.fault .arity)
      | cons argument arguments =>
          have finish (value : Value) : BreakFrameAction (do
              let values ← evalArguments fuel config environment vars parameters arguments
              pure (value :: values)) := by
            apply breakFrame_bind
            · exact previous.arguments _ _ _ _
            · intro _; exact breakFrame_pure _
          cases argument with
          | byVal expression =>
              simp only [evalArguments]
              apply breakFrame_bind
              · exact previous.value _ _
              · intro value; exact finish value
          | byRef mutability place =>
              simp only [evalArguments]
              apply breakFrame_bind
              · exact previous.place _ _
              · intro location
                apply breakFrame_bind
                · exact breakFrame_pure _
                · intro value; exact finish value
          | construct expression =>
              simp only [evalArguments]
              split
              · apply breakFrame_bind
                · apply breakFrame_materializeProducer
                  exact previous.value _ _
                · intro materialized
                  have finishCarrier (carrier : Carrier) : BreakFrameAction (do
                      let value ← carrierValue carrier
                      let values ← evalArguments fuel config environment vars parameters arguments
                      pure (value :: values)) := by
                    apply breakFrame_bind
                    · exact breakFrame_carrierValue carrier
                    · intro value; exact finish value
                  cases materialized with
                  | none =>
                      apply breakFrame_bind
                      · apply breakFrame_constructLocal
                        intro destination; exact previous.build _ _ _
                      · intro carrier; exact finishCarrier carrier
                  | some source =>
                      apply breakFrame_bind
                      · exact breakFrame_materializedDestination _ _ _ _ _ _ _
                      · intro destination
                        apply breakFrame_bind
                        · exact breakFrame_publishCarriers _ _
                        · intro ignored
                          apply breakFrame_bind
                          · exact breakFrame_pure _
                          · intro carrier; exact finishCarrier carrier
              · apply breakFrame_bind
                · exact breakFrame_stop _
                · intro value; exact finish value

private theorem breakFrame_callableChannels (channels : List Channel) (results : List ResultDescriptor)
    (origin : Goose.Core.OriginId) :
    BreakFrameAction ((channels.zip results).mapM fun (channel, result) => do
      match result.request, channel with
      | .register, _ => pure (Channel.register result.ty)
      | .value, .construct incoming | .elementRun, .construct incoming =>
        let destination ← liftConstruction origin (renewReceivingDestination incoming)
        liftConstruction origin (adaptDestinationType destination result.ty)
        pure (.construct destination)
      | .value, .register _ | .elementRun, .register _ => fault .shape
      | _, .completion _ => fault .flow) := by
  apply breakFrame_listMapM
  intro pair
  rcases pair with ⟨channel, descriptor⟩
  rcases descriptor with ⟨ty, request, named⟩
  cases request <;> cases channel <;> evaluation_frame_basic

private theorem breakFrame_renewCallableChannels (channels : List Channel) (origin : Goose.Core.OriginId) :
    BreakFrameAction (channels.mapM fun channel => match channel with
      | .register ty => pure (Channel.register ty)
      | .construct destination => do
          pure (Channel.construct (← liftConstruction origin (renewReceivingDestination destination)))
      | .completion _ => fault .flow) := by
  apply breakFrame_listMapM
  intro channel
  cases channel <;> evaluation_frame_basic

theorem invokeCall_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId) :
    BreakFrameAction (invokeCall (fuel + 1) config environment context arguments channels origin) := by
  simp only [invokeCall]
  apply breakFrame_bind
  · exact breakFrame_getImplementation config context
  · intro pair
    rcases pair with ⟨id, implementation⟩
    split
    · exact breakFrame_fault_bind _ _
    · apply breakFrame_bind
      · exact breakFrame_callableChannels channels implementation.results.toList origin
      · intro callable
        apply breakFrame_bind
        · exact previous.arguments environment implementation.vars implementation.params.toList arguments
        · intro values
          apply breakFrame_bind
          · exact breakFrame_renewCallableChannels callable origin
          · intro renewed
            apply breakFrame_bind
            · exact breakFrame_get
            · intro snapshot
              split
              · exact breakFrame_timeout_bind _
              · apply breakFrame_bind
                · exact breakFrame_freshAct
                · intro act
                  apply breakFrame_allocateActivation
                  apply breakFrame_bind
                  · exact previous.activation _ _ _ _
                  · intro carriers
                    exact breakFrame_deliverCarriers _ _ _ _ _

theorem enterActivation_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) (origin : Goose.Core.OriginId) :
    BreakFrameAction (enterActivation (fuel + 1) config environment pre body origin) := by
  simp only [enterActivation]
  evaluation_frame previous

theorem buildElement_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (element : Ty) (expression : Expr) :
    BreakFrameAction (buildElement (fuel + 1) config environment destination element expression) := by
  simp only [buildElement]
  evaluation_frame previous

theorem pushValue_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) :
    BreakFrameAction (pushValue (fuel + 1) config environment owner expression origin) := by
  simp only [pushValue]
  evaluation_frame previous

theorem evalPrintArg_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (argument : PrintArg) :
    BreakFrameAction (evalPrintArg (fuel + 1) config environment argument) := by
  cases argument <;> simp only [evalPrintArg] <;> evaluation_frame previous

end Goose.Proofs.ConstructionDelivery
