import Goose.Proofs.ConstructionGhostSyntaxFuel
import Goose.Proofs.ConstructionGhostInvocationEventChunks

namespace Goose.Proofs.ConstructionGhostSyntaxAggregateEvents
open Goose.Construct Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocation
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSyntaxFuel
open Goose.Proofs.ConstructionGhostInvocationEvents Goose.Proofs.ConstructionGhostInvocationEventChunks

theorem aggregate_syntaxEventChunks (fuel : Nat) (config : EvalConfig) (closed : ClosedModuleWithTails config)
    (environment : RuntimeActivation) (path : List Nat) (expression : Expr) (operands : List Expr)
    (before : ExecutionState) (shape : ValueAggregate expression operands)
    (children : ∀ operand ∈ operands, ValueSyntax config operand) :
    ∃ mapped visits chunks,
      OperandReplay (evalValue fuel config environment) 0 operands [] before mapped visits ∧
      (∀ visit ∈ visits, SourceHistory config fuel (path ++ [visit.ordinal])
        (.value environment visit.operand) visit.before visit.outcome) ∧
      visits.map Invocation.operand = operands.take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧ ChunksAlign visits chunks ∧
      (Goose.Proofs.Exit.stepState (evalValue (fuel + 1) config environment expression before)).construction.events =
        before.construction.events ++ chunks.flatten := by
  obtain ⟨mapped, visits, replay, histories, ordered, once, segments⟩ :=
    aggregate_fuelInvocationEvents fuel config environment path expression operands before shape
      (fun operand member => (syntaxFuel_existsWithTails fuel config closed).value environment operand (children operand member))
  obtain ⟨chunks, aligned, finalEq⟩ := invocationEvents_chunks segments
  exact ⟨mapped, visits, chunks, replay, histories, ordered, once, aligned, finalEq⟩

#print axioms aggregate_syntaxEventChunks
end Goose.Proofs.ConstructionGhostSyntaxAggregateEvents
