import Goose.Proofs.ConstructionGhostBuilderCallEvents
import Goose.Proofs.ConstructionGhostDeclarationFallback

namespace Goose.Proofs.ConstructionGhostBuilderCallOccurrence
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostDeclarationFallback Goose.Proofs.ConstructionGhostBuilderCallEvents

def BuilderCallOccurrence (incoming destination : Goose.Core.DestinationId) (origin : Goose.Core.OriginId)
    (before ready : ExecutionState) : Prop :=
  liftConstruction origin (renewReceivingDestination incoming) before = .ok destination ready

theorem BuilderCallOccurrence.unique {incoming first second : Goose.Core.DestinationId} {origin : Goose.Core.OriginId}
    {before firstReady secondReady : ExecutionState} (left : BuilderCallOccurrence incoming first origin before firstReady)
    (right : BuilderCallOccurrence incoming second origin before secondReady) : first = second ∧ firstReady = secondReady := by
  unfold BuilderCallOccurrence at left right
  rw [left] at right
  cases right
  exact ⟨rfl, rfl⟩

theorem builderCall_history_or_earlyTerminal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (path : List Nat)
    (history : SourceHistory config (fuel + 1) path (.builder environment incoming (.call context arguments origin)) before
      (buildExpr (fuel + 1) config environment incoming (.call context arguments origin) before)) :
    (∃ destination ready, BuilderCallOccurrence incoming destination origin before ready ∧
      (∀ other otherReady, BuilderCallOccurrence incoming other origin before otherReady → destination = other ∧ ready = otherReady) ∧
      SourceHistory config fuel (path ++ [0]) (.channelCall environment context arguments [.construct destination] origin) ready
        (invokeCall fuel config environment context arguments [.construct destination] origin ready) ∧
      EventPrefix (Goose.Proofs.Exit.stepState (invokeCall fuel config environment context arguments [.construct destination] origin ready)).construction.events
        (Goose.Proofs.Exit.stepState (buildExpr (fuel + 1) config environment incoming (.call context arguments origin) before)).construction.events) ∨
    ((∃ terminal : DeclarationTerminal, buildExpr (fuel + 1) config environment incoming (.call context arguments origin) before = terminal.step) ∧
      ¬ ∃ destination ready, BuilderCallOccurrence incoming destination origin before ready) := by
  cases renewed : liftConstruction origin (renewReceivingDestination incoming) before with
  | ok destination ready =>
      left
      refine ⟨destination, ready, renewed, ?_, ?_, builderCall_sourcePrefix fuel config environment incoming destination context arguments origin before ready renewed⟩
      · intro other otherReady otherOccurrence
        exact BuilderCallOccurrence.unique renewed otherOccurrence
      · exact builderCall_child_history history fuel environment incoming destination context arguments origin ready rfl rfl renewed
  | stop reason state =>
      right
      constructor
      · refine ⟨.stopped reason state, ?_⟩
        simp [buildExpr, expressionOrigin, bind, renewed, DeclarationTerminal.step]
      · rintro ⟨destination, ready, reached⟩
        unfold BuilderCallOccurrence at reached
        rw [renewed] at reached
        cases reached
  | escape address carriers state =>
      right
      constructor
      · refine ⟨.escaped address carriers state, ?_⟩
        simp [buildExpr, expressionOrigin, bind, renewed, DeclarationTerminal.step]
      · rintro ⟨destination, ready, reached⟩
        unfold BuilderCallOccurrence at reached
        rw [renewed] at reached
        cases reached
  | jump target kind state =>
      right
      constructor
      · refine ⟨.jumped target kind state, ?_⟩
        simp [buildExpr, expressionOrigin, bind, renewed, DeclarationTerminal.step]
      · rintro ⟨destination, ready, reached⟩
        unfold BuilderCallOccurrence at reached
        rw [renewed] at reached
        cases reached

#print axioms BuilderCallOccurrence.unique
#print axioms builderCall_history_or_earlyTerminal
end Goose.Proofs.ConstructionGhostBuilderCallOccurrence
