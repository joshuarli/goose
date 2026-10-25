import Goose.Proofs.ExitExecutionActivationChannelsProduce

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem buildElement_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (element : Ty) (expression : Expr) :
    PreservesActivationChannels
      (buildElement (fuel + 1) config environment destination element expression) := by
  simp only [buildElement]
  activation_channels_helper_eval previousFresh previous config

end Goose.Proofs.ExitExecution
