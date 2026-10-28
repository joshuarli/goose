import Goose.Proofs.ConstructionGhostSourceTransition

namespace Goose.Proofs.ConstructionGhostRegisterProducer
open Goose.Construct Goose.Proofs.ConstructionGhostSourceTransition

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

#print axioms registerCompletion_history
#print axioms registerCompletion_source
#print axioms registerProducer_source
end Goose.Proofs.ConstructionGhostRegisterProducer
