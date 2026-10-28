import Goose.Proofs.ConstructionGhostSyntaxFuel
import Goose.Proofs.ConstructionExecutionEventPrefix

namespace Goose.Proofs.ConstructionGhostAssignmentHistory
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionExecutionProtocol Goose.Proofs.ConstructionExecutionEventPrefixProtocol

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

def assignmentSyntax : SourceOperation α → Option (RuntimeActivation × Place × Expr × Goose.Core.OriginId)
  | .statement environment (.assign place expression origin) => some (environment, place, expression, origin)
  | _ => none

theorem assignment_place_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (place : Place) (expression : Expr) (origin : Goose.Core.OriginId)
    (fuelEq : fuel = sourceFuel + 1)
    (operationEq : assignmentSyntax operation = some (environment, place, expression, origin)) :
    SourceHistory config sourceFuel (path ++ [0]) (.place environment place) before (evalPlace sourceFuel config environment place before) := by
  cases history <;> simp_all [assignmentSyntax]

theorem assignment_value_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (place : Place) (expression : Expr) (origin : Goose.Core.OriginId)
    (location : Goose.Core.Loc) (ready : ExecutionState) (fuelEq : fuel = sourceFuel + 1)
    (operationEq : assignmentSyntax operation = some (environment, place, expression, origin))
    (placed : evalPlace sourceFuel config environment place before = .ok location ready) :
    SourceHistory config sourceFuel (path ++ [1]) (.value environment expression) ready (evalValue sourceFuel config environment expression ready) := by
  cases history <;> simp_all [assignmentSyntax]

theorem assignment_value_sourcePrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (place : Place) (expression : Expr) (origin : Goose.Core.OriginId) (before ready : ExecutionState)
    (location : Goose.Core.Loc) (placed : evalPlace fuel config environment place before = .ok location ready) :
    EventPrefix (Goose.Proofs.Exit.stepState (evalValue fuel config environment expression ready)).construction.events
      (Goose.Proofs.Exit.stepState (execStmt (fuel + 1) config environment (.assign place expression origin) before)).construction.events := by
  simp only [execStmt, bind, placed]
  cases result : evalValue fuel config environment expression ready with
  | ok value state =>
      apply (eventPrefix_iff_isPrefix _ _).mpr
      have kept : PreservesConstructionInvariant (PrefixInvariant state.construction.events)
          (do writeLoc fuel config.layout location value; pure (Flow.normal .unit)) := by
        apply preservesConstructionInvariant_bind
        · exact preservesConstructionInvariant_writeLoc _ _ _ _
        · intro ignored; exact preservesConstructionInvariant_pure _
      simpa [result, bind, Goose.Proofs.Exit.stepState, ExecutionInvariant, PrefixInvariant] using kept state List.prefix_rfl
  | stop | escape | jump => simp [result, Goose.Proofs.Exit.stepState, eventPrefix_refl]

def terminalFlow {α : Type} : ExecutionStep α → Option (ExecutionStep Flow)
  | .ok _ _ => none
  | .stop reason state => some (.stop reason state)
  | .escape address carriers state => some (.escape address carriers state)
  | .jump target kind state => some (.jump target kind state)

theorem assignment_sourceClassification (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (place : Place) (expression : Expr) (origin : Goose.Core.OriginId) (before : ExecutionState)
    (history : SourceHistory config (fuel + 1) path (.statement environment (.assign place expression origin)) before
      (execStmt (fuel + 1) config environment (.assign place expression origin) before)) :
    SourceHistory config fuel (path ++ [0]) (.place environment place) before (evalPlace fuel config environment place before) ∧
    ((∃ location ready, evalPlace fuel config environment place before = .ok location ready ∧
      SourceHistory config fuel (path ++ [1]) (.value environment expression) ready (evalValue fuel config environment expression ready) ∧
      EventPrefix (Goose.Proofs.Exit.stepState (evalValue fuel config environment expression ready)).construction.events
        (Goose.Proofs.Exit.stepState (execStmt (fuel + 1) config environment (.assign place expression origin) before)).construction.events) ∨
     (∃ terminal, terminalFlow (evalPlace fuel config environment place before) = some terminal ∧
       execStmt (fuel + 1) config environment (.assign place expression origin) before = terminal)) := by
  refine ⟨assignment_place_history history fuel environment place expression origin rfl rfl, ?_⟩
  cases placed : evalPlace fuel config environment place before with
  | ok location ready =>
      exact Or.inl ⟨location, ready, rfl,
        assignment_value_history history fuel environment place expression origin location ready rfl rfl placed,
        assignment_value_sourcePrefix fuel config environment place expression origin before ready location placed⟩
  | stop reason state => exact Or.inr ⟨.stop reason state, rfl, by simp [execStmt, bind, placed]⟩
  | escape address carriers state => exact Or.inr ⟨.escape address carriers state, rfl, by simp [execStmt, bind, placed]⟩
  | jump target kind state => exact Or.inr ⟨.jump target kind state, rfl, by simp [execStmt, bind, placed]⟩

#print axioms assignment_sourceClassification
#print axioms assignment_value_sourcePrefix
#print axioms assignment_place_history
#print axioms assignment_value_history
end Goose.Proofs.ConstructionGhostAssignmentHistory
