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
  case valueFirstStatement =>
    rename_i shape child
    cases shape <;> simp_all [assignmentSyntax]
  case leafStatement =>
    rename_i shape
    cases shape <;> simp_all [assignmentSyntax]

theorem assignment_value_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (place : Place) (expression : Expr) (origin : Goose.Core.OriginId)
    (location : Goose.Core.Loc) (ready : ExecutionState) (fuelEq : fuel = sourceFuel + 1)
    (operationEq : assignmentSyntax operation = some (environment, place, expression, origin))
    (placed : evalPlace sourceFuel config environment place before = .ok location ready) :
    SourceHistory config sourceFuel (path ++ [1]) (.value environment expression) ready (evalValue sourceFuel config environment expression ready) := by
  cases history <;> simp_all [assignmentSyntax]
  case valueFirstStatement =>
    rename_i shape child
    cases shape <;> simp_all [assignmentSyntax]
  case leafStatement =>
    rename_i shape
    cases shape <;> simp_all [assignmentSyntax]

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

def valueFirstOperand : Stmt → Option Expr
  | .rebind _ expression _ | .assertS expression _ | .exit expression _ => some expression
  | _ => none

def valueFirstSyntax : SourceOperation α → Option (RuntimeActivation × Expr)
  | .statement environment statement => (valueFirstOperand statement).map (environment, ·)
  | _ => none

theorem valueFirst_operand_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (expression : Expr) (fuelEq : fuel = sourceFuel + 1)
    (operationEq : valueFirstSyntax operation = some (environment, expression)) :
    SourceHistory config sourceFuel (path ++ [0]) (.value environment expression) before
      (evalValue sourceFuel config environment expression before) := by
  cases history <;> simp_all [valueFirstSyntax, valueFirstOperand]
  case valueFirstStatement =>
    rename_i shape child
    cases shape <;> simp_all [valueFirstSyntax, valueFirstOperand]
  case leafStatement =>
    rename_i shape
    cases shape <;> simp_all [valueFirstSyntax, valueFirstOperand]

theorem valueFirst_sourcePrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (statement : Stmt) (expression : Expr) (before : ExecutionState) (shape : ValueFirstStatement statement expression) :
    EventPrefix (Goose.Proofs.Exit.stepState (evalValue fuel config environment expression before)).construction.events
      (Goose.Proofs.Exit.stepState (execStmt (fuel + 1) config environment statement before)).construction.events := by
  cases shape with
  | rebind localVar expression origin =>
      simp only [execStmt, bind]
      cases result : evalValue fuel config environment expression before with
      | ok value state =>
          apply (eventPrefix_iff_isPrefix _ _).mpr
          have kept : PreservesConstructionInvariant (PrefixInvariant state.construction.events)
              (do writeLoc fuel config.layout ⟨← rootOf environment localVar, []⟩ value; pure (Flow.normal .unit)) := by
            let previous := evaluation_preservesConstructionInvariant (predicate := PrefixInvariant state.construction.events) fuel config
            protocol_eval previous
          simpa [result, bind, Goose.Proofs.Exit.stepState, ExecutionInvariant, PrefixInvariant] using kept state List.prefix_rfl
      | stop | escape | jump => simp [result, Goose.Proofs.Exit.stepState, eventPrefix_refl]
  | assertion expression origin =>
      simp only [execStmt, bind]
      cases result : evalValue fuel config environment expression before with
      | ok value state =>
          apply (eventPrefix_iff_isPrefix _ _).mpr
          have kept : PreservesConstructionInvariant (PrefixInvariant state.construction.events)
              (do if (← expectBool value) then pure (Flow.normal .unit) else abortAt .assert origin) := by
            let previous := evaluation_preservesConstructionInvariant (predicate := PrefixInvariant state.construction.events) fuel config
            protocol_eval previous
          simpa [result, bind, Goose.Proofs.Exit.stepState, ExecutionInvariant, PrefixInvariant] using kept state List.prefix_rfl
      | stop | escape | jump => simp [result, Goose.Proofs.Exit.stepState, eventPrefix_refl]
  | exit expression origin =>
      simp only [execStmt, bind]
      cases result : evalValue fuel config environment expression before with
      | ok value state =>
          apply (eventPrefix_iff_isPrefix _ _).mpr
          have kept : PreservesConstructionInvariant (PrefixInvariant state.construction.events)
              (do let (_, code) ← expectInt value; EvalM.stop (α := Flow) (.exit code)) := by
            let previous := evaluation_preservesConstructionInvariant (predicate := PrefixInvariant state.construction.events) fuel config
            protocol_eval previous
          simpa [result, bind, Goose.Proofs.Exit.stepState, ExecutionInvariant, PrefixInvariant] using kept state List.prefix_rfl
      | stop | escape | jump => simp [result, Goose.Proofs.Exit.stepState, eventPrefix_refl]

#print axioms valueFirst_sourcePrefix
#print axioms valueFirst_operand_history
#print axioms assignment_sourceClassification
#print axioms assignment_value_sourcePrefix
#print axioms assignment_place_history
#print axioms assignment_value_history
end Goose.Proofs.ConstructionGhostAssignmentHistory
