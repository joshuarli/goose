import Goose.Proofs.ConstructionAcceptedParameterScopeExit

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem execActivationBody_bound_registerTail (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (pre : List (Nat × Value)) (scope : Nat) (statements : List Stmt) (expression : Expr) (ty : Ty)
    (before boundState middle : ExecutionState) (channels : activation.channels = [.register ty])
    (bound : bindAll activation.act before.nextScope pre (ownershipResultScopeState activation scope before) = .ok () boundState)
    (normal : execStmts fuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes }
      statements boundState = .ok (.normal .unit) middle) :
    execActivationBody (fuel + 1) config activation pre ⟨scope, statements, some expression⟩ before =
      match withCompletionChannels [.register ty] (expressionOrigin expression)
        (fun channels => evalProduce fuel config
          { activation with scopes := (scope, before.nextScope) :: activation.scopes } channels expression) middle with
      | .ok carriers after => .ok carriers (releaseScopeState activation scope before.nextScope after)
      | .stop reason after => .stop reason after
      | .escape target carriers after => .escape target carriers (releaseScopeState activation scope before.nextScope after)
      | .jump target kind after => .jump target kind (releaseScopeState activation scope before.nextScope after) := by
  simp only [ownershipResultScopeState, beq_iff_eq] at bound
  simp only [channels] at normal ⊢
  cases produced : withCompletionChannels [.register ty] (expressionOrigin expression)
      (fun channels => evalProduce fuel config
        { activation with scopes := (scope, before.nextScope) :: activation.scopes, channels := [.register ty] } channels expression) middle <;>
    simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope,
      bound, channels, normal, produced, releaseScope]

#print axioms execActivationBody_bound_registerTail
end Goose.Proofs.ConstructionAcceptedExecution
