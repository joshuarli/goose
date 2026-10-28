import Goose.Proofs.ConstructionGhostProducerChannel

namespace Goose.Proofs.ConstructionGhostBlockProducerTransition
open Goose.Construct

def prepareBlockProducerChannels (channels : List Channel) (origin : Goose.Core.OriginId) : EvalM (List Channel) :=
  channels.mapM fun channel => match channel with
    | .register ty => pure (.register ty)
    | .construct destination => do pure (.construct (← liftConstruction origin (renewReceivingDestination destination)))
    | .completion token => pure (.completion token)

def blockProducerStart (environment : RuntimeActivation) (channels : List Channel) (before : ExecutionState) : ExecutionState :=
  let target : BreakTarget := ⟨before.nextScope, environment.act, .block, channels⟩
  { before with nextScope := before.nextScope + 1, breaks := target :: before.breaks }

end Goose.Proofs.ConstructionGhostBlockProducerTransition
