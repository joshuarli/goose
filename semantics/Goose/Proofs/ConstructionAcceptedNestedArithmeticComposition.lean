import Goose.Proofs.ConstructionAcceptedNestedComposition

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem nestedValueUnary_compose (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (integer : Goose.Core.IntTy) (operation : Goose.Core.UnOp) (expression : Expr) (origin : Nat) (before : ExecutionState)
    (operandSafe : NestedValueOutcome config accepted frame ambient types live (.int integer)
      (evalValue fuel config frame.interpretation.environment expression before)) :
    NestedValueOutcome config accepted frame ambient types live (.int integer)
      (evalValue (fuel + 1) config frame.interpretation.environment (.un operation expression origin) before) := by
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
      cases computed : Goose.Core.evalUn config.profile operation integer number with
      | error reason =>
        simp only [NestedValueOutcome, evalValue, execution, bind, expectInt, pure, computed, abortAt, EvalM.stop, Goose.Proofs.Exit.stepState]
        exact ⟨operandSafe.1, operandSafe.2.1, trivial⟩
      | ok result =>
        simp only [NestedValueOutcome, evalValue, execution, bind, expectInt, pure, computed, Goose.Proofs.Exit.stepState]
        exact ⟨operandSafe.1, operandSafe.2.1, .integer integer result, .integer integer result⟩

theorem nestedValueBinary_compose (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (integer : Goose.Core.IntTy) (operation : Goose.Core.BinOp) (left right : Expr) (origin : Nat) (before : ExecutionState)
    (leftSafe : NestedValueOutcome config accepted frame ambient types live (.int integer)
      (evalValue fuel config frame.interpretation.environment left before))
    (rightSafe : ∀ state, AcceptedWorld config frame.initialized state ambient types live [] [] →
      AcceptedFrame config accepted frame state types →
      NestedValueOutcome config accepted frame ambient types live (.int integer)
        (evalValue fuel config frame.interpretation.environment right state)) :
    NestedValueOutcome config accepted frame ambient types live (.int integer)
      (evalValue (fuel + 1) config frame.interpretation.environment (.bin operation left right origin) before) := by
  cases leftRun : evalValue fuel config frame.interpretation.environment left before with
  | stop reason after =>
    simp only [NestedValueOutcome, leftRun, Goose.Proofs.Exit.stepState] at leftSafe
    simpa [NestedValueOutcome, evalValue, leftRun, bind, Goose.Proofs.Exit.stepState] using leftSafe
  | escape address carriers after | jump target kind after =>
    simp only [NestedValueOutcome, leftRun] at leftSafe
    exact leftSafe.2.2.elim
  | ok value middle =>
    simp only [NestedValueOutcome, leftRun, Goose.Proofs.Exit.stepState] at leftSafe
    cases represented : leftSafe.2.2.1 with
    | stored => contradiction
    | integer _ first =>
      have rightResult := rightSafe middle leftSafe.1 leftSafe.2.1
      cases rightRun : evalValue fuel config frame.interpretation.environment right middle with
      | stop reason after =>
        simp only [NestedValueOutcome, rightRun, Goose.Proofs.Exit.stepState] at rightResult
        simpa [NestedValueOutcome, evalValue, leftRun, rightRun, bind, expectInt, pure, Goose.Proofs.Exit.stepState] using rightResult
      | escape address carriers after | jump target kind after =>
        simp only [NestedValueOutcome, rightRun] at rightResult
        exact rightResult.2.2.elim
      | ok value after =>
        simp only [NestedValueOutcome, rightRun, Goose.Proofs.Exit.stepState] at rightResult
        cases represented : rightResult.2.2.1 with
        | stored => contradiction
        | integer _ second =>
          cases computed : Goose.Core.evalBin config.profile operation integer first second with
          | error reason =>
            simp only [NestedValueOutcome, evalValue, leftRun, rightRun, bind, expectInt, pure, sameIntType,
              beq_self_eq_true, ↓reduceIte, computed, abortAt, EvalM.stop, Goose.Proofs.Exit.stepState]
            exact ⟨rightResult.1, rightResult.2.1, trivial⟩
          | ok result =>
            simp only [NestedValueOutcome, evalValue, leftRun, rightRun, bind, expectInt, pure, sameIntType,
              beq_self_eq_true, ↓reduceIte, computed, Goose.Proofs.Exit.stepState]
            exact ⟨rightResult.1, rightResult.2.1, .integer integer result, .integer integer result⟩

#print axioms nestedValueBinary_compose
#print axioms nestedValueUnary_compose
end Goose.Proofs.ConstructionAcceptedExecution
