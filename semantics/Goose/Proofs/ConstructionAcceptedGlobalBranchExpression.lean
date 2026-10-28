import Goose.Proofs.ConstructionAcceptedScalarConditional

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem execBlock_literalExpression_transition (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (scope : Nat) (statement tail : Expr) (statementValue tailValue : Value) (origin : Nat)
    (statementLiteral : ScalarLiteral statement statementValue) (tailLiteral : ScalarLiteral tail tailValue)
    (before : ExecutionState) :
    execBlock (fuel + 4) config environment [] [] ⟨scope, [.expr statement origin], some tail⟩ before =
      .ok (.normal tailValue) (releaseScopeState environment scope before.nextScope { before with nextScope := before.nextScope + 1 }) := by
  cases statementLiteral <;> cases tailLiteral <;>
    simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, execStmts,
      execStmt, evalValue, releaseScope, releaseScopeState]

theorem execBlock_literalExpression_world (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (scope : Nat) (statement tail : Expr) (statementValue tailValue : Value) (origin : Nat)
    (statementLiteral : ScalarLiteral statement statementValue) (tailLiteral : ScalarLiteral tail tailValue)
    (id : Nat) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (world : AcceptedWorld config id before ambient types live [] []) :
    ∃ nextLive,
      let outcome := execBlock fuel config environment [] [] ⟨scope, [.expr statement origin], some tail⟩ before
      AcceptedWorld config id (Goose.Proofs.Exit.stepState outcome) ambient types nextLive [] [] ∧
      (match outcome with | .ok flow _ => flow = .normal tailValue | .stop .. => True | _ => False) := by
  cases fuel with
  | zero =>
    simp only [execBlock, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    exact ⟨live, world, trivial⟩
  | succ fuel =>
    let entered := { before with nextScope := before.nextScope + 1 }
    have enteredWorld := (freshScope_acceptedWorld config id before ambient types live world).2
    cases fuel with
    | zero =>
      have stopped : execBlock 1 config environment [] [] ⟨scope, [.expr statement origin], some tail⟩ before = .stop .timeout entered := by
        simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, execStmts, timeout, EvalM.stop, entered]
      simp only [stopped, Goose.Proofs.Exit.stepState]
      exact ⟨live, enteredWorld, trivial⟩
    | succ fuel =>
      cases fuel with
      | zero =>
        have stopped : execBlock 2 config environment [] [] ⟨scope, [.expr statement origin], some tail⟩ before = .stop .timeout entered := by
          simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, execStmts, execStmt, timeout, EvalM.stop, entered]
        simp only [stopped, Goose.Proofs.Exit.stepState]
        exact ⟨live, enteredWorld, trivial⟩
      | succ fuel =>
        cases fuel with
        | zero =>
          have stopped : execBlock 3 config environment [] [] ⟨scope, [.expr statement origin], some tail⟩ before = .stop .timeout entered := by
            simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, execStmts, execStmt, evalValue, timeout, EvalM.stop, entered]
          simp only [stopped, Goose.Proofs.Exit.stepState]
          exact ⟨live, enteredWorld, trivial⟩
        | succ fuel =>
          have done := execBlock_literalExpression_transition fuel config environment scope statement tail statementValue tailValue origin
            statementLiteral tailLiteral before
          have released := enteredWorld.releaseScope config id entered ambient types live [] [] environment scope before.nextScope
          simp only [done, Goose.Proofs.Exit.stepState]
          exact ⟨_, released, trivial⟩

theorem execBlock_literalExpression_futureGlobals (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (scope : Nat) (statement tail : Expr) (statementValue tailValue : Value) (origin : Nat)
    (statementLiteral : ScalarLiteral statement statementValue) (tailLiteral : ScalarLiteral tail tailValue)
    (id : Nat) (before : ExecutionState) (empty : environment.vars = #[]) (clear : FutureGlobalsClear config id before) :
    FutureGlobalsClear config id (Goose.Proofs.Exit.stepState
      (execBlock fuel config environment [] [] ⟨scope, [.expr statement origin], some tail⟩ before)) := by
  have nextClear : FutureGlobalsClear config id { before with nextScope := before.nextScope + 1 } := clear
  cases fuel with
  | zero => simpa [execBlock, timeout, EvalM.stop, Goose.Proofs.Exit.stepState] using clear
  | succ fuel =>
    cases fuel with
    | zero =>
      simpa [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, execStmts,
        timeout, EvalM.stop, Goose.Proofs.Exit.stepState] using nextClear
    | succ fuel =>
      cases fuel with
      | zero =>
        simpa [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, execStmts, execStmt,
          timeout, EvalM.stop, Goose.Proofs.Exit.stepState] using nextClear
      | succ fuel =>
        cases fuel with
        | zero =>
          simpa [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, execStmts, execStmt,
            evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState] using nextClear
        | succ fuel =>
          rw [execBlock_literalExpression_transition fuel config environment scope statement tail statementValue tailValue origin
            statementLiteral tailLiteral before]
          simp only [Goose.Proofs.Exit.stepState]
          intro global future inside
          simpa [releaseScopeState, empty] using clear global future inside

#print axioms execBlock_literalExpression_futureGlobals
#print axioms execBlock_literalExpression_world
#print axioms execBlock_literalExpression_transition
end Goose.Proofs.ConstructionAcceptedExecution
