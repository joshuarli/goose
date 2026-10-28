import Goose.Proofs.ConstructionScalarTailExecution

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem evalProduce_register_scalar {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation) (state : ExecutionState) (ty : Ty) :
    evalProduce (fuel + 1) config environment [.register ty] expression state =
      (do let value ← evalValue fuel config environment expression; pure [Carrier.register value]) state := by
  cases evaluated : evalValue fuel config environment expression state <;> cases form with
  | numeric form =>
    cases form with
    | scalar form =>
      cases form with
      | scalar form => cases form <;> simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
      | not form => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
    | unary operation origin form => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
    | conversion kind target origin form => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
  | binary operation origin left right => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
  | comparison operation left right => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
  | conjunction left right => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
  | disjunction left right => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
  | not form => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
  | unary operation origin form => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
  | conversion kind target origin form => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]

theorem completion_register_scalar {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation) (state : ExecutionState) (ty : Ty) :
    withCompletionChannels [.register ty] (expressionOrigin expression)
      (fun channels => evalProduce (fuel + 1) config environment channels expression) state =
      (do let value ← evalValue fuel config environment expression; pure [Carrier.register value]) state := by
  have produced := evalProduce_register_scalar form fuel config environment state ty
  cases evaluated : evalValue fuel config environment expression state <;>
    simp [withCompletionChannels, materializeOwnedCarriers, bind, pure, produced, evaluated]

theorem execActivationBody_register_scalar_tail {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt)
    (before middle : ExecutionState) (ty : Ty) (channels : activation.channels = [.register ty])
    (normal : execStmts (fuel + 1) config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements
      (ownershipResultScopeState activation scope before) = .ok (.normal .unit) middle) :
    execActivationBody (fuel + 2) config activation [] ⟨scope, statements, some expression⟩ before =
      match evalValue fuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes } expression middle with
      | .ok value after => .ok [.register value] (releaseScopeState activation scope before.nextScope after)
      | .stop reason after => .stop reason after
      | .escape target carriers after => .escape target carriers (releaseScopeState activation scope before.nextScope after)
      | .jump target kind after => .jump target kind (releaseScopeState activation scope before.nextScope after) := by
  have tail := completion_register_scalar form fuel config
    { activation with scopes := (scope, before.nextScope) :: activation.scopes } middle ty
  simp only [ownershipResultScopeState, beq_iff_eq, channels] at normal
  simp only [channels] at tail
  simp only [channels] at ⊢
  cases evaluated : evalValue fuel config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes, channels := [.register ty] } expression middle <;>
    simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope,
      bindAll, channels, beq_iff_eq, normal, tail, evaluated, releaseScope]

theorem execActivationBody_register_statements_stopped (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt) (expression : Expr)
    (before after : ExecutionState) (reason : Goose.Core.Stop)
    (stopped : execStmts (fuel + 1) config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements
      (ownershipResultScopeState activation scope before) = .stop reason after) :
    execActivationBody (fuel + 2) config activation [] ⟨scope, statements, some expression⟩ before = .stop reason after := by
  simp only [ownershipResultScopeState, beq_iff_eq] at stopped
  simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, stopped]

#print axioms execActivationBody_register_statements_stopped
#print axioms execActivationBody_register_scalar_tail
#print axioms evalProduce_register_scalar
#print axioms completion_register_scalar
end Goose.Proofs.ConstructionAcceptedExecution
