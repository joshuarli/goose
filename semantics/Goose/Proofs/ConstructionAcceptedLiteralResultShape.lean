import Goose.Proofs.ConstructionAcceptedGlobalAssignResultBlock

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem execResultBlock_integerTail_shape (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (state : ExecutionState) (scope : Nat) (statements : List Stmt) (intTy : Goose.Core.IntTy) (literal : Int)
    (normal : ∀ flow after,
      execStmts fuel config { environment with scopes := (scope, state.nextScope) :: environment.scopes }
        statements (ownershipResultScopeState environment scope state) = .ok flow after → flow = .normal .unit)
    (result : Flow × List Carrier) (after : ExecutionState)
    (executed : execResultBlock (fuel + 2) config environment [.register (.int intTy)]
      ⟨scope, statements, some (.lit intTy literal)⟩ state = .ok result after) :
    result = (.normal .unit, [.register (.int intTy literal)]) := by
  cases statement : execStmts fuel config { environment with scopes := (scope, state.nextScope) :: environment.scopes }
      statements (ownershipResultScopeState environment scope state) with
  | stop reason middle | escape address carriers middle | jump target kind middle =>
    simp only [ownershipResultScopeState, beq_iff_eq] at statement
    simp [execResultBlock, execResultBlockWith, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure,
      withScope, bindAll, ownershipResultScopeState, statement, releaseScope] at executed
  | ok flow middle =>
    have same := normal flow middle statement
    subst flow
    simp only [ownershipResultScopeState, beq_iff_eq] at statement
    cases fuel with
    | zero =>
      simp [execResultBlock, execResultBlockWith, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure,
        withScope, bindAll, ownershipResultScopeState, statement, evalProduce, timeout, EvalM.stop] at executed
    | succ fuel =>
      cases fuel <;> simp [execResultBlock, execResultBlockWith, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure,
        withScope, bindAll, ownershipResultScopeState, statement, evalProduce, evalValue, selectCompletionChannel,
        releaseScope, timeout, EvalM.stop] at executed ⊢
      exact executed.1.symm

#print axioms execResultBlock_integerTail_shape
end Goose.Proofs.ConstructionAcceptedExecution
