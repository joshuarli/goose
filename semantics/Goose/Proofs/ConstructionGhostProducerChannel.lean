import Goose.Construct.Eval
import Goose.Proofs.ConstructionGhostGlobalStep

namespace Goose.Proofs.ConstructionGhostProducerChannel
open Goose.Construct

def prepareProducerCallChannels (environment : RuntimeActivation) (expression : Expr) (channels : List Channel) : EvalM (List Channel) := do
  let channels ← channels.mapM fun channel => match channel with
    | .register ty => pure (.register ty)
    | .construct id => do pure (.construct (← liftConstruction (expressionOrigin expression) (renewReceivingDestination id)))
    | .completion token => pure (.completion token)
  channels.mapM (selectCompletionChannel environment expression)

theorem producerCall_transition (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId)
    (before : ExecutionState) :
    evalProduce (fuel + 1) config environment channels (.call context arguments origin) before =
      (prepareProducerCallChannels environment (.call context arguments origin) channels >>= fun selected =>
        invokeCall fuel config environment context arguments selected origin) before := by
  simp only [evalProduce, prepareProducerCallChannels, Goose.Proofs.ConstructionGhostGlobalStep.evalM_bind_assoc]
  rfl

#print axioms producerCall_transition
end Goose.Proofs.ConstructionGhostProducerChannel
