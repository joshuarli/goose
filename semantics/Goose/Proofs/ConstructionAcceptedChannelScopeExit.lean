import Goose.Proofs.ConstructionAcceptedParameterScopeExit

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem execActivationBody_bound_channelTail (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (pre : List (Nat × Value)) (scope : Nat) (statements : List Stmt) (expression : Expr)
    (before boundState middle : ExecutionState)
    (bound : bindAll activation.act before.nextScope pre (ownershipResultScopeState activation scope before) = .ok () boundState)
    (normal : execStmts fuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes }
      statements boundState = .ok (.normal .unit) middle) :
    execActivationBody (fuel + 1) config activation pre ⟨scope, statements, some expression⟩ before =
      match withCompletionChannels activation.channels (expressionOrigin expression)
        (fun channels => evalProduce fuel config
          { activation with scopes := (scope, before.nextScope) :: activation.scopes } channels expression) middle with
      | .ok carriers after => .ok carriers (releaseScopeState activation scope before.nextScope after)
      | .stop reason after => .stop reason after
      | .escape target carriers after => .escape target carriers (releaseScopeState activation scope before.nextScope after)
      | .jump target kind after => .jump target kind (releaseScopeState activation scope before.nextScope after) := by
  simp only [ownershipResultScopeState, beq_iff_eq] at bound
  cases produced : withCompletionChannels activation.channels (expressionOrigin expression)
      (fun channels => evalProduce fuel config
        { activation with scopes := (scope, before.nextScope) :: activation.scopes } channels expression) middle <;>
    simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope,
      bound, normal, produced, releaseScope]

#print axioms execActivationBody_bound_channelTail
end Goose.Proofs.ConstructionAcceptedExecution
