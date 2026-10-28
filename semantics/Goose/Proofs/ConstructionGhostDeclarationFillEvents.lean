import Goose.Proofs.ConstructionGhostDeclarationSourceSegments

namespace Goose.Proofs.ConstructionGhostDeclarationFillEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostSourceFuel Goose.Proofs.ConstructionGhostSourceTransition
open Goose.Proofs.ConstructionGhostDeclarationOnce Goose.Proofs.ConstructionGhostDeclarationOccurrenceEvents

theorem fixedFill_declaration_sourceEvents (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (localVar : Goose.Core.VarId) (element : Ty) (count : Nat) (operand : Expr)
    (expressionOrigin origin : Goose.Core.OriginId) (before ready : ExecutionState)
    (fixed : (Ty.arr element count).nonfixed = false)
    (occurrence : DeclarationOccurrence (fuel + 1) config environment localVar
      (.fill (.arr element count) operand expressionOrigin) origin before none ready)
    (supported : FuelSupport config fuel (.value environment operand)) :
    SourceHistory config fuel ((path ++ [0]) ++ [0]) (.value environment operand) ready
      (evalValue fuel config environment operand ready) ∧
    evalValue (fuel + 1) config environment (.fill (.arr element count) operand expressionOrigin) ready =
      fillResult count (evalValue fuel config environment operand ready) ∧
    ∃ source continuation : List Goose.Core.ConstructionEvent,
      (Goose.Proofs.Exit.stepState (evalValue fuel config environment operand ready)).construction.events =
        ready.construction.events ++ source ∧
      (Goose.Proofs.Exit.stepState (execStmt (fuel + 2) config environment
        (.letS localVar (.fill (.arr element count) operand expressionOrigin) origin) before)).construction.events =
          ready.construction.events ++ source ++ continuation := by
  have execution : evalValue (fuel + 1) config environment (.fill (.arr element count) operand expressionOrigin) ready =
      fillResult count (evalValue fuel config environment operand ready) := by
    simp only [evalValue, fixed, Bool.false_eq_true, ↓reduceIte, bind, fillResult]
    cases evalValue fuel config environment operand ready <;> rfl
  have sourcePrefix := (evaluation_keepsEventPrefix fuel config).value environment operand ready
  have continuationPrefix := DeclarationOccurrence.sourcePrefix occurrence
  rw [execution] at continuationPrefix
  have same : (Goose.Proofs.Exit.stepState (fillResult count (evalValue fuel config environment operand ready))).construction.events =
      (Goose.Proofs.Exit.stepState (evalValue fuel config environment operand ready)).construction.events := by
    cases evalValue fuel config environment operand ready <;> rfl
  rw [same] at continuationPrefix
  obtain ⟨source, sourceEq⟩ := sourcePrefix
  obtain ⟨continuation, continuationEq⟩ := continuationPrefix
  refine ⟨fuelHistory_exists fuel config _ _ ready supported, execution, source, continuation, sourceEq, ?_⟩
  rw [continuationEq, sourceEq]

#print axioms fixedFill_declaration_sourceEvents
end Goose.Proofs.ConstructionGhostDeclarationFillEvents
