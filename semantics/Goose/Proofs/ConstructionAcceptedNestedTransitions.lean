import Goose.Proofs.ConstructionAcceptedNestedScope

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem evalValue_conditional_conditionStop (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (condition : Expr) (yes no : Block) (origin : Nat) (before after : ExecutionState) (reason : Goose.Core.Stop)
    (executed : evalValue fuel config environment condition before = .stop reason after) :
    evalValue (fuel + 1) config environment (.ifE condition yes no origin) before = .stop reason after := by
  simp [evalValue, executed, bind]

theorem evalValue_conditional_branchStop (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (condition : Expr) (yes no : Block) (origin : Nat) (before middle after : ExecutionState) (choice : Bool)
    (reason : Goose.Core.Stop) (conditionRun : evalValue fuel config environment condition before = .ok (.bool choice) middle)
    (branchRun : execBlock fuel config environment [] [] (if choice then yes else no) middle = .stop reason after) :
    evalValue (fuel + 1) config environment (.ifE condition yes no origin) before = .stop reason after := by
  cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at branchRun <;>
    simp [evalValue, conditionRun, expectBool, bind, pure, branchRun]

theorem evalValue_conditional_branchNormal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (condition : Expr) (yes no : Block) (origin : Nat) (before middle after : ExecutionState) (choice : Bool)
    (value : Value) (conditionRun : evalValue fuel config environment condition before = .ok (.bool choice) middle)
    (branchRun : execBlock fuel config environment [] [] (if choice then yes else no) middle = .ok (.normal value) after) :
    evalValue (fuel + 1) config environment (.ifE condition yes no origin) before = .ok value after := by
  cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at branchRun <;>
    simp [evalValue, conditionRun, expectBool, bind, pure, branchRun]

#print axioms evalValue_conditional_conditionStop
#print axioms evalValue_conditional_branchStop
#print axioms evalValue_conditional_branchNormal
end Goose.Proofs.ConstructionAcceptedExecution
