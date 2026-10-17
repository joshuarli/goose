import Goose.Proofs.ExitExecutionCompletion

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

local macro "fresh_channel" : tactic => `(tactic|
  repeat' first
    | exact preservesFresh_pure _
    | exact preservesFresh_stop _
    | exact preservesFresh_get
    | exact preservesFresh_lift _ _
    | exact stateQuery_preservesFresh _ (stateQuery_receivingDestination _)
    | exact stateQuery_preservesFresh _ (stateQuery_getDestination _)
    | exact stateQuery_preservesFresh _ (stateQuery_exitSource _ _ _)
    | apply preservesFresh_bind
    | dsimp only
    | split
    | intro)

theorem preservesFresh_selectCompletionChannel (source : RuntimeActivation) (operand : Expr)
    (channel : Channel) : PreservesFresh (selectCompletionChannel source operand channel) := by
  cases channel <;> simp only [selectCompletionChannel]
  all_goals fresh_channel

theorem preservesFresh_prepareNamedCarrier (origin : Goose.Core.OriginId)
    (incoming : Goose.Core.DestinationId) (stored : StoredValue) :
    PreservesFresh (prepareNamedCarrier origin incoming stored) := by
  unfold prepareNamedCarrier
  fresh_channel

theorem preservesFresh_prepareNamedCarrierAt (origin : Goose.Core.OriginId)
    (token : ExitReservationId) (incoming : Goose.Core.DestinationId) (stored : StoredValue) :
    PreservesFresh (prepareNamedCarrierAt origin token incoming stored) := by
  unfold prepareNamedCarrierAt
  fresh_channel

#print axioms preservesFresh_prepareNamedCarrierAt

end Goose.Proofs.ExitExecution
