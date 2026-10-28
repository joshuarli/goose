import Goose.Proofs.ConstructionGhostDeclarationSourceSegments
import Goose.Proofs.ConstructionGhostInvocationEventChunks
import Goose.Proofs.ConstructionGhostSourceAggregate

namespace Goose.Proofs.ConstructionGhostDeclarationAggregateEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionInvocationReplay
open Goose.Proofs.ConstructionGhostInvocation Goose.Proofs.ConstructionGhostInvocationEvents
open Goose.Proofs.ConstructionGhostInvocationEventChunks Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostSourceFuel Goose.Proofs.ConstructionGhostSourceAggregate
open Goose.Proofs.ConstructionGhostDeclarationOnce Goose.Proofs.ConstructionGhostDeclarationOccurrenceEvents

theorem aggregate_declaration_sourceEvents (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (localVar : Goose.Core.VarId) (expression : Expr) (operands : List Expr) (origin : Goose.Core.OriginId)
    (before ready : ExecutionState) (shape : ValueAggregate expression operands)
    (occurrence : DeclarationOccurrence (fuel + 1) config environment localVar expression origin before none ready)
    (supported : ∀ operand ∈ operands, FuelSupport config fuel (.value environment operand)) :
    ∃ mapped visits chunks continuation,
      OperandReplay (evalValue fuel config environment) 0 operands [] ready mapped visits ∧
      (∀ visit ∈ visits, SourceHistory config fuel ((path ++ [0]) ++ [visit.ordinal])
        (.value environment visit.operand) visit.before visit.outcome) ∧
      visits.map Invocation.operand = operands.take visits.length ∧ (visits.map Invocation.ordinal).Nodup ∧
      ChunksAlign visits chunks ∧
      (Goose.Proofs.Exit.stepState (evalValue (fuel + 1) config environment expression ready)).construction.events =
        ready.construction.events ++ chunks.flatten ∧
      (Goose.Proofs.Exit.stepState (execStmt (fuel + 2) config environment (.letS localVar expression origin) before)).construction.events =
        ready.construction.events ++ chunks.flatten ++ continuation := by
  obtain ⟨mapped, visits, replay, children, ordered, once, segments⟩ :=
    aggregate_fuelInvocationEvents fuel config environment (path ++ [0]) expression operands ready shape supported
  obtain ⟨chunks, aligned, sourceEvents⟩ := invocationEvents_chunks segments
  have preserved := DeclarationOccurrence.sourcePrefix occurrence
  obtain ⟨continuation, finalEq⟩ := preserved
  refine ⟨mapped, visits, chunks, continuation, replay, children, ordered, once, aligned, sourceEvents, ?_⟩
  rw [finalEq, sourceEvents]

#print axioms aggregate_declaration_sourceEvents
end Goose.Proofs.ConstructionGhostDeclarationAggregateEvents
