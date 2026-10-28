import Goose.Proofs.ConstructionGhostDeclarationOccurrenceEvents

namespace Goose.Proofs.ConstructionGhostDeclarationSourceSegments
open Goose.Construct Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostDeclarationOnce Goose.Proofs.ConstructionGhostDeclarationOccurrenceEvents

def sourceEvents (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation) (expression : Expr)
    (destination : Option Goose.Core.DestinationId) (ready : ExecutionState) : List Goose.Core.ConstructionEvent :=
  match destination with
  | none => (Goose.Proofs.Exit.stepState (evalValue fuel config environment expression ready)).construction.events
  | some destination => (Goose.Proofs.Exit.stepState (buildExpr fuel config environment destination expression ready)).construction.events

theorem occurrence_sourceSegments {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {localVar : Goose.Core.VarId} {expression : Expr} {origin : Goose.Core.OriginId} {before ready : ExecutionState}
    {destination : Option Goose.Core.DestinationId}
    (occurrence : DeclarationOccurrence fuel config environment localVar expression origin before destination ready) :
    ∃ source continuation : List Goose.Core.ConstructionEvent,
      sourceEvents fuel config environment expression destination ready = ready.construction.events ++ source ∧
      (Goose.Proofs.Exit.stepState (execStmt (fuel + 1) config environment (.letS localVar expression origin) before)).construction.events =
        ready.construction.events ++ source ++ continuation ∧
      ∀ other, sourceEvents fuel config environment expression destination ready = ready.construction.events ++ other → source = other := by
  have first : EventPrefix ready.construction.events (sourceEvents fuel config environment expression destination ready) := by
    cases destination with
    | none => exact (evaluation_keepsEventPrefix fuel config).value environment expression ready
    | some destination => exact (evaluation_keepsEventPrefix fuel config).build environment destination expression ready
  have second : EventPrefix (sourceEvents fuel config environment expression destination ready)
      (Goose.Proofs.Exit.stepState (execStmt (fuel + 1) config environment (.letS localVar expression origin) before)).construction.events := by
    have actual := DeclarationOccurrence.sourcePrefix occurrence
    cases destination <;> exact actual
  obtain ⟨source, sourceEq⟩ := first
  obtain ⟨continuation, finalEq⟩ := second
  refine ⟨source, continuation, sourceEq, ?_, ?_⟩
  · rw [finalEq, sourceEq]
  · intro other otherEq
    exact (List.append_right_inj _).mp (sourceEq.symm.trans otherEq)

#print axioms occurrence_sourceSegments
end Goose.Proofs.ConstructionGhostDeclarationSourceSegments
