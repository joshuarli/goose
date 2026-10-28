import Goose.Proofs.ConstructionAcceptedNestedArithmeticComposition
import Goose.Proofs.ConstructionAcceptedBinaryComplete

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem nestedValueShortCircuit_compose (conjunction : Bool) (fuel : Nat) (config : EvalConfig)
    (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (left right : Expr) (before : ExecutionState)
    (leftSafe : NestedValueOutcome config accepted frame ambient types live .bool
      (evalValue fuel config frame.interpretation.environment left before))
    (rightSafe : ∀ state, AcceptedWorld config frame.initialized state ambient types live [] [] →
      AcceptedFrame config accepted frame state types →
      NestedValueOutcome config accepted frame ambient types live .bool
        (evalValue fuel config frame.interpretation.environment right state)) :
    NestedValueOutcome config accepted frame ambient types live .bool
      (evalValue (fuel + 1) config frame.interpretation.environment (scalarShortCircuit conjunction left right) before) := by
  cases leftRun : evalValue fuel config frame.interpretation.environment left before with
  | stop reason after =>
    simp only [NestedValueOutcome, leftRun, Goose.Proofs.Exit.stepState] at leftSafe
    cases conjunction <;> simpa [scalarShortCircuit, NestedValueOutcome, evalValue, leftRun, bind, Goose.Proofs.Exit.stepState] using leftSafe
  | escape address carriers after | jump target kind after =>
    simp only [NestedValueOutcome, leftRun] at leftSafe
    exact leftSafe.2.2.elim
  | ok value middle =>
    simp only [NestedValueOutcome, leftRun, Goose.Proofs.Exit.stepState] at leftSafe
    cases represented : leftSafe.2.2.1 with
    | stored => contradiction
    | boolean first =>
      cases conjunction <;> cases first <;>
        simp only [scalarShortCircuit, Bool.false_eq_true, ↓reduceIte, NestedValueOutcome, evalValue, leftRun,
          bind, expectBool, pure, Goose.Proofs.Exit.stepState]
      all_goals first
        | exact ⟨leftSafe.1, leftSafe.2.1, .boolean _, .boolean _⟩
        | skip
      all_goals
        have rightResult := rightSafe middle leftSafe.1 leftSafe.2.1
        cases rightRun : evalValue fuel config frame.interpretation.environment right middle with
        | stop reason after =>
          simp only [NestedValueOutcome, rightRun, Goose.Proofs.Exit.stepState] at rightResult
          simpa [rightRun, bind, Goose.Proofs.Exit.stepState] using rightResult
        | escape address carriers after | jump target kind after =>
          simp only [NestedValueOutcome, rightRun] at rightResult
          exact rightResult.2.2.elim
        | ok value after =>
          simp only [NestedValueOutcome, rightRun, Goose.Proofs.Exit.stepState] at rightResult
          cases represented : rightResult.2.2.1 with
          | stored => contradiction
          | boolean second =>
            simpa [rightRun, bind, expectBool, pure, Goose.Proofs.Exit.stepState] using rightResult

theorem nestedValueComparison_compose (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (operandTy : Ty) (operandKind : operandTy = .bool ∨ ∃ integer, operandTy = .int integer)
    (operation : Goose.Core.CmpOp) (left right : Expr) (before : ExecutionState)
    (leftSafe : NestedValueOutcome config accepted frame ambient types live operandTy
      (evalValue fuel config frame.interpretation.environment left before))
    (rightSafe : ∀ state, AcceptedWorld config frame.initialized state ambient types live [] [] →
      AcceptedFrame config accepted frame state types →
      NestedValueOutcome config accepted frame ambient types live operandTy
        (evalValue fuel config frame.interpretation.environment right state)) :
    NestedValueOutcome config accepted frame ambient types live .bool
      (evalValue (fuel + 1) config frame.interpretation.environment (.cmp operation left right) before) := by
  cases leftRun : evalValue fuel config frame.interpretation.environment left before with
  | stop reason after =>
    simp only [NestedValueOutcome, leftRun, Goose.Proofs.Exit.stepState] at leftSafe
    simpa [NestedValueOutcome, evalValue, leftRun, bind, Goose.Proofs.Exit.stepState] using leftSafe
  | escape address carriers after | jump target kind after =>
    simp only [NestedValueOutcome, leftRun] at leftSafe
    exact leftSafe.2.2.elim
  | ok first middle =>
    simp only [NestedValueOutcome, leftRun, Goose.Proofs.Exit.stepState] at leftSafe
    have rightResult := rightSafe middle leftSafe.1 leftSafe.2.1
    cases rightRun : evalValue fuel config frame.interpretation.environment right middle with
    | stop reason after =>
      simp only [NestedValueOutcome, rightRun, Goose.Proofs.Exit.stepState] at rightResult
      simpa [NestedValueOutcome, evalValue, leftRun, rightRun, bind, Goose.Proofs.Exit.stepState] using rightResult
    | escape address carriers after | jump target kind after =>
      simp only [NestedValueOutcome, rightRun] at rightResult
      exact rightResult.2.2.elim
    | ok second after =>
      simp only [NestedValueOutcome, rightRun, Goose.Proofs.Exit.stepState] at rightResult
      rcases operandKind with boolean | ⟨integer, integerType⟩
      · subst operandTy
        cases leftRep : leftSafe.2.2.1 with
        | stored => contradiction
        | boolean first =>
          cases rightRep : rightResult.2.2.1 with
          | stored => contradiction
          | boolean second =>
            simp only [NestedValueOutcome, evalValue, leftRun, rightRun, bind, comparable, pure, Goose.Proofs.Exit.stepState]
            exact ⟨rightResult.1, rightResult.2.1, .boolean _, .boolean _⟩
      · subst operandTy
        cases leftRep : leftSafe.2.2.1 with
        | stored => contradiction
        | integer _ first =>
          cases rightRep : rightResult.2.2.1 with
          | stored => contradiction
          | integer _ second =>
            simp only [NestedValueOutcome, evalValue, leftRun, rightRun, bind, comparable, sameIntType,
              beq_self_eq_true, ↓reduceIte, pure, Goose.Proofs.Exit.stepState]
            exact ⟨rightResult.1, rightResult.2.1, .boolean _, .boolean _⟩

theorem nestedValueConversion_compose (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (source target : Goose.Core.IntTy) (kind : Goose.Core.ConvKind) (expression : Expr) (origin : Nat) (before : ExecutionState)
    (operandSafe : NestedValueOutcome config accepted frame ambient types live (.int source)
      (evalValue fuel config frame.interpretation.environment expression before)) :
    NestedValueOutcome config accepted frame ambient types live (.int target)
      (evalValue (fuel + 1) config frame.interpretation.environment (.conv kind (.int target) expression origin) before) := by
  cases execution : evalValue fuel config frame.interpretation.environment expression before with
  | stop reason after =>
    simp only [NestedValueOutcome, execution, Goose.Proofs.Exit.stepState] at operandSafe
    simpa [NestedValueOutcome, evalValue, execution, bind, Goose.Proofs.Exit.stepState] using operandSafe
  | escape address carriers after | jump target kind after =>
    simp only [NestedValueOutcome, execution] at operandSafe
    exact operandSafe.2.2.elim
  | ok value after =>
    simp only [NestedValueOutcome, execution, Goose.Proofs.Exit.stepState] at operandSafe
    cases represented : operandSafe.2.2.1 with
    | stored => contradiction
    | integer _ number =>
      cases computed : Goose.Core.evalConv config.profile kind source target number with
      | error reason =>
        simp only [NestedValueOutcome, evalValue, execution, bind, expectInt, pure, computed, abortAt, EvalM.stop, Goose.Proofs.Exit.stepState]
        exact ⟨operandSafe.1, operandSafe.2.1, trivial⟩
      | ok result =>
        simp only [NestedValueOutcome, evalValue, execution, bind, expectInt, pure, computed, Goose.Proofs.Exit.stepState]
        exact ⟨operandSafe.1, operandSafe.2.1, .integer target result, .integer target result⟩

#print axioms nestedValueConversion_compose
#print axioms nestedValueComparison_compose
#print axioms nestedValueShortCircuit_compose
end Goose.Proofs.ConstructionAcceptedExecution
