import Goose.Proofs.ConstructionAcceptedRegisterCallTail

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem execActivationBody_boundStatements_stopped (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (scope : Nat) (pre : List (Nat × Value)) (statements : List Stmt) (expression : Expr)
    (before boundState after : ExecutionState) (reason : Goose.Core.Stop)
    (bound : bindAll activation.act before.nextScope pre (ownershipResultScopeState activation scope before) = .ok () boundState)
    (stopped : execStmts (fuel + 1) config { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements
      boundState = .stop reason after) :
    execActivationBody (fuel + 2) config activation pre ⟨scope, statements, some expression⟩ before = .stop reason after := by
  have bound' := bound
  simp [ownershipResultScopeState] at bound'
  simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope,
    beq_iff_eq, bound', stopped]

#print axioms execActivationBody_boundStatements_stopped
end Goose.Proofs.ConstructionAcceptedExecution
