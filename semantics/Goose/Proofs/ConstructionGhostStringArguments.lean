import Goose.Proofs.ConstructionGhostProducerString
import Goose.Proofs.ConstructionGhostStringLoop

namespace Goose.Proofs.ConstructionGhostStringArguments
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostStringLoop
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionInitializerLoopReplay

theorem stringArgument_histories (fuel : Nat) (config : EvalConfig) (closed : ClosedModuleWithTails config)
    (environment : RuntimeActivation) (incoming destination : Goose.Core.DestinationId) (ty : Ty)
    (arguments : List PrintArg) (origin : Goose.Core.OriginId) (before ready : ExecutionState) (path : List Nat)
    (renewed : liftConstruction origin (renewReceivingDestination incoming) before = .ok destination ready)
    (supported : ∀ argument ∈ arguments, PrintArgumentSyntax config argument) :
    ∃ outcome visits,
      OperandReplay (stringArgumentAction fuel config environment destination origin) 0 arguments [] ready outcome visits ∧
      visits.map Invocation.operand = arguments.take visits.length ∧ (visits.map Invocation.ordinal).Nodup ∧
      (∀ visit ∈ visits, SourceHistory config fuel (path ++ [visit.ordinal]) (.printArgument environment visit.operand)
        visit.before (evalPrintArg fuel config environment visit.operand visit.before)) ∧
      buildExpr (fuel + 1) config environment incoming (.str ty arguments origin) before =
        protectDestination origin destination (fun _ =>
          match discardValues outcome with
          | .ok _ state => receivingAction origin destination finishDestination state
          | .stop reason state => .stop reason state
          | .escape address carriers state => .escape address carriers state
          | .jump target kind state => .jump target kind state) ready := by
  obtain ⟨outcome, visits, replay, ordered, once, execution⟩ :=
    string_execution_replay fuel config environment incoming destination ty arguments origin before ready renewed
  refine ⟨outcome, visits, replay, ordered, once, ?_, execution⟩
  intro visit member
  have inMapped : visit.operand ∈ visits.map Invocation.operand := List.mem_map_of_mem member
  rw [ordered] at inMapped
  have inArguments : visit.operand ∈ arguments := List.mem_of_mem_take inMapped
  exact fuelHistory_exists fuel config _ (path ++ [visit.ordinal]) visit.before
    ((syntaxFuel_existsWithTails fuel config closed).printArgument environment visit.operand (supported visit.operand inArguments))

#print axioms stringArgument_histories
end Goose.Proofs.ConstructionGhostStringArguments
