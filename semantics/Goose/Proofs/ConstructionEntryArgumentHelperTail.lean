import Goose.Proofs.ConstructionEntryCallIdentity
import Goose.Proofs.ConstructionByteEntryStopped

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem evalProduce_empty_argumentCall (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (contextId origin : Nat) (arguments : List Arg) (state : ExecutionState) :
    evalProduce (fuel + 1) config environment [] (.call contextId arguments origin) state =
      invokeCall fuel config environment contextId arguments [] origin state := by
  simp [evalProduce, bind, pure]

theorem completion_empty_argumentCall (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (contextId origin : Nat) (arguments : List Arg) (state : ExecutionState)
    (shape : match invokeCall fuel config environment contextId arguments [] origin state with
      | .ok carriers _ => carriers = [] | .stop .. => True | _ => False) :
    withCompletionChannels [] origin
      (fun channels => evalProduce (fuel + 1) config environment channels (.call contextId arguments origin)) state =
      invokeCall fuel config environment contextId arguments [] origin state := by
  have produced := evalProduce_empty_argumentCall fuel config environment contextId origin arguments state
  cases evaluated : invokeCall fuel config environment contextId arguments [] origin state with
  | ok carriers after =>
    simp only [evaluated] at shape
    subst carriers
    simp [withCompletionChannels, completionChannelSetup, materializeOwnedCarriers, bind, pure, produced, evaluated]
  | stop reason after => simp [withCompletionChannels, completionChannelSetup, bind, pure, produced, evaluated]
  | escape address carriers after | jump target kind after => simp only [evaluated] at shape

theorem execActivationBody_argumentHelperTail (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (scope : Nat) (statements : List Stmt) (contextId origin : Nat) (arguments : List Arg) (before middle : ExecutionState)
    (channels : activation.channels = [])
    (normal : execStmts (fuel + 1) config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements
      (ownershipResultScopeState activation scope before) = .ok (.normal .unit) middle)
    (shape : match invokeCall fuel config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes } contextId arguments [] origin middle with
      | .ok carriers _ => carriers = [] | .stop .. => True | _ => False) :
    execActivationBody (fuel + 2) config activation [] ⟨scope, statements, some (.call contextId arguments origin)⟩ before =
      match invokeCall fuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes } contextId arguments [] origin middle with
      | .ok _ after => .ok [] (releaseScopeState activation scope before.nextScope after)
      | .stop reason after => .stop reason after
      | .escape target carriers after => .escape target carriers (releaseScopeState activation scope before.nextScope after)
      | .jump target kind after => .jump target kind (releaseScopeState activation scope before.nextScope after) := by
  have tail := completion_empty_argumentCall fuel config
    { activation with scopes := (scope, before.nextScope) :: activation.scopes } contextId origin arguments middle shape
  simp only [ownershipResultScopeState, beq_iff_eq, channels] at normal
  simp only [channels] at tail shape ⊢
  cases evaluated : invokeCall fuel config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes, channels := [] } contextId arguments [] origin middle <;>
    simp only [evaluated] at shape <;>
    simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope,
      bindAll, channels, beq_iff_eq, normal, expressionOrigin, tail, evaluated, releaseScope, shape]

#print axioms execActivationBody_argumentHelperTail
#print axioms completion_empty_argumentCall
end Goose.Proofs.ConstructionAcceptedExecution
