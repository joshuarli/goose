import Goose.Proofs.ConstructionInitializerLoopReplay
import Goose.Proofs.ConstructionGhostGlobalStep

namespace Goose.Proofs.ConstructionGhostStringLoop
open Goose.Construct Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionInitializerLoopReplay

def stringArgumentAction (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) (argument : PrintArg) : EvalM Unit := do
  let bytes ← evalPrintArg fuel config environment argument
  for byte in bytes.data do receivingAction origin destination (fun current => writeElement current ⟨#[byte]⟩)

theorem string_execution_replay (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming destination : Goose.Core.DestinationId) (ty : Ty) (arguments : List PrintArg) (origin : Goose.Core.OriginId)
    (before ready : ExecutionState)
    (renewed : liftConstruction origin (renewReceivingDestination incoming) before = .ok destination ready) :
    ∃ outcome visits,
      OperandReplay (stringArgumentAction fuel config environment destination origin) 0 arguments [] ready outcome visits ∧
      visits.map Invocation.operand = arguments.take visits.length ∧ (visits.map Invocation.ordinal).Nodup ∧
      buildExpr (fuel + 1) config environment incoming (.str ty arguments origin) before =
        protectDestination origin destination (fun _ =>
          match discardValues outcome with
          | .ok _ state => receivingAction origin destination finishDestination state
          | .stop reason state => .stop reason state
          | .escape address carriers state => .escape address carriers state
          | .jump target kind state => .jump target kind state) ready := by
  obtain ⟨outcome, visits, replay, loop, ordered, once⟩ := initializerLoop_replay
    (stringArgumentAction fuel config environment destination origin) arguments ready
  refine ⟨outcome, visits, replay, ordered, once, ?_⟩
  simp only [buildExpr, expressionOrigin, bind, renewed, protectDestination]
  simp only [stringArgumentAction, Goose.Proofs.ConstructionGhostGlobalStep.evalM_bind_assoc] at loop
  simp only [bind, pure] at loop
  simp only [pure]
  rw [loop]
  cases outcome <;> rfl

#print axioms string_execution_replay
end Goose.Proofs.ConstructionGhostStringLoop
