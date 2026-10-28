import Goose.Proofs.ConstructionGhostCallHistoryInversion

namespace Goose.Proofs.ConstructionGhostDirectCallHistory
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual

def directCallSyntax : SourceOperation α → Option (RuntimeActivation × Goose.Core.ContextId × List Arg × Goose.Core.OriginId)
  | .callWith environment context arguments origin => some (environment, context, arguments, origin)
  | _ => none

theorem directCall_activation_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome)
    (sourceFuel : Nat) (environment : RuntimeActivation) (contextId : Goose.Core.ContextId)
    (arguments : List Arg) (origin : Goose.Core.OriginId) (context : Context) (implementation : Impl)
    (values : List Value) (ready : ExecutionState) (fuelEq : fuel = sourceFuel + 1)
    (operationEq : directCallSyntax operation = some (environment, contextId, arguments, origin))
    (contextFound : config.module.contexts[contextId]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (argumentsResult : evalArguments sourceFuel config environment implementation.vars implementation.params.toList arguments before = .ok values ready)
    (depth : ready.activations.length < Goose.Core.maxCallDepth) :
    let activation : RuntimeActivation := ⟨context.impl, ready.nextAct, implementation.vars, [], []⟩
    let activated := { ready with nextAct := ready.nextAct + 1, activations := activation :: ready.activations }
    let pre := (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
    SourceHistory config sourceFuel (path ++ [1]) (.boundActivation activation pre implementation.body origin) activated
      (enterActivation sourceFuel config activation pre implementation.body origin activated) := by
  cases history <;> simp_all [directCallSyntax]
  case callWith =>
    rename_i activationHistory argumentsHistory
    have actual := argumentsHistory.sound
    simp only [execute] at actual
    apply activationHistory values ready
    · rw [← actual]
      exact argumentsResult
    · exact depth

def emptyCallSyntax : SourceOperation α → Option (RuntimeActivation × Goose.Core.ContextId × Goose.Core.OriginId)
  | .call environment context origin => some (environment, context, origin)
  | _ => none

theorem emptyCall_activation_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome)
    (sourceFuel : Nat) (environment : RuntimeActivation) (contextId : Goose.Core.ContextId)
    (origin : Goose.Core.OriginId) (context : Context) (implementation : Impl)
    (fuelEq : fuel = sourceFuel + 2) (operationEq : emptyCallSyntax operation = some (environment, contextId, origin))
    (contextFound : config.module.contexts[contextId]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (depth : before.activations.length < Goose.Core.maxCallDepth) :
    let activation : RuntimeActivation := ⟨context.impl, before.nextAct, implementation.vars, [], []⟩
    let activated := { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }
    SourceHistory config (sourceFuel + 1) (path ++ [0]) (.activation activation implementation.body origin) activated
      (enterActivation (sourceFuel + 1) config activation [] implementation.body origin activated) := by
  cases history <;> simp_all [emptyCallSyntax]
  case callDepth => omega
  case callEnter =>
    rename_i child
    have actual := child.sound
    simp only [execute] at actual
    rw [actual]
    exact child

def activationSyntax : SourceOperation α → Option (RuntimeActivation × Block × Goose.Core.OriginId)
  | .activation activation body origin => some (activation, body, origin)
  | _ => none

theorem activation_body_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome)
    (sourceFuel : Nat) (activation : RuntimeActivation) (body : Block) (origin : Goose.Core.OriginId) (implementation : Impl)
    (fuelEq : fuel = sourceFuel + 1) (operationEq : activationSyntax operation = some (activation, body, origin))
    (implemented : config.module.impls[activation.implementation]? = some implementation) :
    SourceHistory config sourceFuel (path ++ [0]) (.activationBody activation body) before
      (execActivationBody sourceFuel config activation [] body before) := by
  cases history <;> simp_all [activationSyntax]

def activationBodySyntax : SourceOperation α → Option (RuntimeActivation × Block)
  | .activationBody activation body => some (activation, body)
  | _ => none

theorem activation_statements_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome)
    (sourceFuel : Nat) (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt)
    (fuelEq : fuel = sourceFuel + 1) (operationEq : activationBodySyntax operation = some (activation, .mk scope statements none)) :
    SourceHistory config sourceFuel (path ++ [0])
      (.statements { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements)
      (Goose.Proofs.ConstructionGhostResultScope.resultScopeStart activation scope before)
      (execStmts sourceFuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements
        (Goose.Proofs.ConstructionGhostResultScope.resultScopeStart activation scope before)) := by
  cases history <;> simp_all [activationBodySyntax]
  case activationBody =>
    rename_i child
    have actual := child.sound
    simp only [execute] at actual
    rw [actual]
    exact child

#print axioms activation_body_history
#print axioms activation_statements_history
#print axioms emptyCall_activation_history
#print axioms directCall_activation_history
end Goose.Proofs.ConstructionGhostDirectCallHistory
