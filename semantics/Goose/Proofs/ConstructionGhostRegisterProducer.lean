import Goose.Proofs.ConstructionGhostSourceTransition
import Goose.Proofs.ConstructionGhostProducerChannel

namespace Goose.Proofs.ConstructionGhostRegisterProducer
open Goose.Construct Goose.Proofs.ConstructionGhostSourceTransition Goose.Proofs.ConstructionGhostProducerChannel

def supportedProducerResult (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (expression : Expr) (channels : List Channel) : EvalM (List Carrier) :=
  match channels with
  | [] => do let _ ← evalValue fuel config environment expression; pure []
  | [.register _] => do pure [.register (← evalValue fuel config environment expression)]
  | [.construct destination] => do
      buildExpr fuel config environment destination expression
      pure [.completed (← completedReceivingDestination destination)]
  | _ => fault .arity

theorem supportedProducer_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (expression : Expr) (before : ExecutionState) (supported : SupportedValue expression) :
    evalProduce (fuel + 1) config environment channels expression before =
      (prepareProducerCallChannels environment expression channels >>= supportedProducerResult fuel config environment expression) before := by
  cases supported <;> simp only [evalProduce, prepareProducerCallChannels, supportedProducerResult,
    Goose.Proofs.ConstructionGhostGlobalStep.evalM_bind_assoc] <;> rfl

def supportedBuilderOperand : Expr → Expr
  | .fill (.arr _ _) operand _ => operand
  | expression => expression

def supportedBuilderNeedsValue : Expr → Bool
  | .fill (.arr element _) _ _ => !element.nonfixed
  | _ => true

theorem supportedBuilderOperand_supported (expression : Expr) (supported : SupportedValue expression) :
    SupportedValue (supportedBuilderOperand expression) := by
  cases supported <;> simp_all [supportedBuilderOperand, SupportedValue.integer, SupportedValue.boolean, SupportedValue.negation]

def supportedBuilderAction (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (expression : Expr) : EvalM Unit :=
  match expression with
  | .fill (.arr element count) operand origin => do
      if element.nonfixed then
        let source ← newDestination config.layout environment.act element .value origin
        buildExpr fuel config environment source operand
        let source ← completedReceivingDestination source
        for _ in [0:count] do repeatElement fuel config.layout destination element source origin
        receivingAction origin destination (fun destination => retireRepeatedSource destination source)
      else
        let value ← evalValue fuel config environment operand
        let bytes ← liftExcept (fixedBytes fuel config.layout element value)
        for _ in [0:count] do receivingAction origin destination (fun destination => writeElement destination bytes)
      receivingAction origin destination finishDestination
  | expression => do
      let value ← evalValue fuel config environment expression
      copyValue fuel config.layout destination value (expressionOrigin expression) none

theorem supportedBuilder_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (expression : Expr) (before : ExecutionState) (supported : SupportedValue expression) :
    buildExpr (fuel + 1) config environment incoming expression before =
      (do let destination ← liftConstruction (expressionOrigin expression) (renewReceivingDestination incoming)
          protectDestination (expressionOrigin expression) destination
            (supportedBuilderAction fuel config environment destination expression)) before := by
  cases supported with
  | integer | boolean | negation => simp only [buildExpr, supportedBuilderAction]
  | fill element count origin fixed child => simp only [buildExpr, supportedBuilderAction]

def registerProducerResult : ExecutionStep Value → ExecutionStep (List Carrier)
  | .ok value state => .ok [.register value] state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem registerProducer_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (ty : Ty) (expression : Expr) (before : ExecutionState) (supported : SupportedValue expression) :
    evalProduce (fuel + 1) config environment [.register ty] expression before =
      registerProducerResult (evalValue fuel config environment expression before) := by
  cases supported <;> simp [evalProduce, List.mapM, List.mapM.loop, bind, pure,
    selectCompletionChannel, registerProducerResult] <;>
    cases evalValue fuel config environment _ before <;> rfl

theorem registerCompletion_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (ty : Ty) (expression : Expr) (before : ExecutionState) (supported : SupportedValue expression) :
    withCompletionChannels [.register ty] (expressionOrigin expression)
      (fun channels => evalProduce (fuel + 1) config environment channels expression) before =
        registerProducerResult (evalValue fuel config environment expression before) := by
  have produced := registerProducer_source fuel config environment ty expression before supported
  cases evaluated : evalValue fuel config environment expression before <;>
    simp_all [withCompletionChannels, completionChannelSetup, materializeOwnedCarriers,
      List.mapM, List.mapM.loop, bind, pure, registerProducerResult, List.forIn_nil]

theorem registerCompletion_history (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (ty : Ty) (expression : Expr) (path : List Nat) (before : ExecutionState) (supported : SupportedValue expression) :
    ∃ outcome, ValueHistory config environment fuel path expression before outcome ∧
      withCompletionChannels [.register ty] (expressionOrigin expression)
        (fun channels => evalProduce (fuel + 1) config environment channels expression) before = registerProducerResult outcome := by
  exact ⟨_, valueHistory_exists fuel config environment path expression before supported,
    registerCompletion_source fuel config environment ty expression before supported⟩

#print axioms supportedBuilderOperand_supported
#print axioms supportedBuilder_source
#print axioms supportedProducer_source
#print axioms registerCompletion_history
#print axioms registerCompletion_source
#print axioms registerProducer_source
end Goose.Proofs.ConstructionGhostRegisterProducer
