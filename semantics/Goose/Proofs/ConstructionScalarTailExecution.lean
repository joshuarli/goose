import Goose.Proofs.ConstructionAcceptedBinaryComplete
import Goose.Proofs.ConstructionAcceptedScopeWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem evalProduce_empty_scalar {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation) (state : ExecutionState) :
    evalProduce (fuel + 1) config environment [] expression state =
      (do let _ ← evalValue fuel config environment expression; pure []) state := by
  cases form with
  | numeric form =>
    cases form with
    | scalar form =>
      cases form with
      | scalar form => cases form <;> simp [evalProduce, bind, pure]
      | not form => simp [evalProduce, bind, pure]
    | unary operation origin form => simp [evalProduce, bind, pure]
    | conversion kind target origin form => simp [evalProduce, bind, pure]
  | binary operation origin left right => simp [evalProduce, bind, pure]
  | comparison operation left right => simp [evalProduce, bind, pure]
  | conjunction left right => simp [evalProduce, bind, pure]
  | disjunction left right => simp [evalProduce, bind, pure]
  | not form => simp [evalProduce, bind, pure]
  | unary operation origin form => simp [evalProduce, bind, pure]
  | conversion kind target origin form => simp [evalProduce, bind, pure]

theorem completion_empty_scalar {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation) (state : ExecutionState) :
    withCompletionChannels [] (expressionOrigin expression)
      (fun channels => evalProduce (fuel + 1) config environment channels expression) state =
      (do let _ ← evalValue fuel config environment expression; pure []) state := by
  have produced := evalProduce_empty_scalar form fuel config environment state
  cases evaluated : evalValue fuel config environment expression state <;>
    simp [withCompletionChannels, materializeOwnedCarriers, bind, pure, produced, evaluated]

theorem execActivationBody_scalar_tail {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt)
    (before middle : ExecutionState) (channels : activation.channels = [])
    (normal : execStmts (fuel + 1) config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements
      (ownershipResultScopeState activation scope before) = .ok (.normal .unit) middle) :
    execActivationBody (fuel + 2) config activation [] ⟨scope, statements, some expression⟩ before =
      match evalValue fuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes } expression middle with
      | .ok _ after => .ok [] (releaseScopeState activation scope before.nextScope after)
      | .stop reason after => .stop reason after
      | .escape target carriers after => .escape target carriers (releaseScopeState activation scope before.nextScope after)
      | .jump target kind after => .jump target kind (releaseScopeState activation scope before.nextScope after) := by
  have tail := completion_empty_scalar form fuel config
    { activation with scopes := (scope, before.nextScope) :: activation.scopes } middle
  simp only [ownershipResultScopeState, beq_iff_eq, channels] at normal
  simp only [channels] at tail
  simp only [channels] at ⊢
  cases evaluated : evalValue fuel config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes, channels := [] } expression middle <;>
    simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope,
      bindAll, channels, ownershipResultScopeState, beq_iff_eq, normal, tail, evaluated, releaseScope]

theorem checkedScalarTail_activation_world {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt) (before middle : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (channels : activation.channels = [])
    (environment : frame.interpretation.environment =
      { activation with scopes := (scope, before.nextScope) :: activation.scopes })
    (normal : execStmts (fuel + 1) config frame.interpretation.environment statements
      (ownershipResultScopeState activation scope before) = .ok (.normal .unit) middle)
    (world : AcceptedWorld config frame.initialized middle ambient types live regions pending)
    (source : AcceptedFrame config accepted frame middle types)
    (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame expression ty roots typingAfter rootsAfter) :
    let outcome := execActivationBody (fuel + 2) config activation [] ⟨scope, statements, some expression⟩ before
    match outcome with
    | .stop _ after => AcceptedWorld config frame.initialized after ambient types live regions pending
    | .ok _ after | .escape _ _ after | .jump _ _ after =>
      AcceptedWorld config frame.initialized after ambient types
        (fun root => live root ∧ (Goose.Proofs.Exit.runtimeScopeRoots activation scope before.nextScope).contains root = false)
        regions pending := by
  have result := evalValue_checked_binary_recursive form fuel config accepted frame middle ambient types live regions pending
    world source ty roots typingAfter rootsAfter checked
  have normal' : execStmts (fuel + 1) config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements
      (ownershipResultScopeState activation scope before) = .ok (.normal .unit) middle := by
    simpa only [environment] using normal
  have execution := execActivationBody_scalar_tail form fuel config activation scope statements before middle channels normal'
  rw [← environment] at execution
  dsimp only
  rw [execution]
  cases evaluated : evalValue fuel config frame.interpretation.environment expression middle with
  | ok value after | escape value carriers after | jump value kind after =>
    simp only [evaluated, Goose.Proofs.Exit.stepState] at result
    have same := result.1
    subst after
    exact world.releaseScope config frame.initialized middle ambient types live regions pending activation scope before.nextScope
  | stop reason after =>
    simp only [evaluated, Goose.Proofs.Exit.stepState] at result
    have same := result.1
    subst after
    exact world

#print axioms checkedScalarTail_activation_world
#print axioms execActivationBody_scalar_tail
#print axioms completion_empty_scalar
#print axioms evalProduce_empty_scalar
end Goose.Proofs.ConstructionAcceptedExecution
