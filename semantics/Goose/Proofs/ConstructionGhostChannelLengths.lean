import Goose.Proofs.ConstructionInvocationReplay

namespace Goose.Proofs.ConstructionGhostChannelLengths
open Goose.Construct Goose.Proofs.ConstructionInvocationReplay

theorem operandReplay_success_length
    (replay : OperandReplay action offset operands accumulator before outcome visits)
    (success : outcome = .ok values after) : values.length = operands.length + accumulator.length := by
  induction replay with
  | done => cases success; simp
  | next head tail ih =>
      have length := ih success
      simp only [List.length_cons] at length ⊢
      omega
  | stopped | escaped | jumped => cases success

theorem channelsFor_success_length (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (results : List ResultDescriptor) (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (channels : List Channel) (executed : channelsFor layout owner results origin before = .ok channels after) :
    channels.length = results.length := by
  let action : ResultDescriptor → EvalM Channel := fun descriptor => match descriptor.request with
    | .register => pure (.register descriptor.ty)
    | .value => do pure (.construct (← newDestination layout owner descriptor.ty .value origin))
    | .elementRun => do pure (.construct (← newDestination layout owner descriptor.ty .elementRun origin))
  obtain ⟨visits, replay⟩ := mapM_replay action results before
  change (results.mapM action) before = .ok channels after at executed
  rw [executed] at replay
  simpa using operandReplay_success_length replay rfl

#print axioms operandReplay_success_length
#print axioms channelsFor_success_length
end Goose.Proofs.ConstructionGhostChannelLengths
