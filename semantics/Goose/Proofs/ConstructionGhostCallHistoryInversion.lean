import Goose.Proofs.ConstructionGhostDeclarationNestedCall

namespace Goose.Proofs.ConstructionGhostCallHistoryInversion
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostCallActivation

def channelCallSyntax : SourceOperation α → Option (RuntimeActivation × Goose.Core.ContextId × List Arg × List Channel × Goose.Core.OriginId)
  | .channelCall environment context arguments channels origin => some (environment, context, arguments, channels, origin)
  | _ => none

theorem call_activation_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome)
    (sourceFuel : Nat) (environment : RuntimeActivation) (context : Goose.Core.ContextId)
    (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (lookupReady argumentsReady valuesReady activationReady : ExecutionState)
    (id : Goose.Core.ImplId) (implementation : Impl) (callableChannels refreshed : List Channel) (values : List Value)
    (fuelEq : fuel = sourceFuel + 1)
    (operationEq : channelCallSyntax operation = some (environment, context, arguments, channels, origin))
    (lookup : getImplementation config context before = .ok (id, implementation) lookupReady)
    (arity : channels.length = implementation.results.size)
    (prepared : prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels argumentsReady)
    (argumentsResult : evalArguments sourceFuel config environment implementation.vars implementation.params.toList arguments argumentsReady = .ok values valuesReady)
    (refresh : refreshCallableChannels callableChannels origin valuesReady = .ok refreshed activationReady)
    (depth : activationReady.activations.length < Goose.Core.maxCallDepth) :
    let activation : RuntimeActivation := ⟨id, activationReady.nextAct, implementation.vars, [], refreshed⟩
    let activated := { activationReady with nextAct := activationReady.nextAct + 1, activations := activation :: activationReady.activations }
    let pre := (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
    SourceHistory config sourceFuel (path ++ [1]) (.boundActivation activation pre implementation.body origin) activated
      (enterActivation sourceFuel config activation pre implementation.body origin activated) := by
  cases history <;> simp_all [channelCallSyntax]
  case channelCall =>
    rename_i activationChildren
    exact activationChildren id implementation lookupReady callableChannels argumentsReady values valuesReady refreshed activationReady
      rfl rfl rfl prepared argumentsResult refresh depth

def boundActivationSyntax : SourceOperation α → Option (RuntimeActivation × List (Goose.Core.VarId × Value) × Block × Goose.Core.OriginId)
  | .boundActivation activation pre body origin => some (activation, pre, body, origin)
  | _ => none

theorem activation_body_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome)
    (sourceFuel : Nat) (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (body : Block) (origin : Goose.Core.OriginId) (implementation : Impl)
    (fuelEq : fuel = sourceFuel + 1)
    (operationEq : boundActivationSyntax operation = some (activation, pre, body, origin))
    (implemented : config.module.impls[activation.implementation]? = some implementation) :
    SourceHistory config sourceFuel (path ++ [0]) (.boundActivationBody activation pre body) before
      (execActivationBody sourceFuel config activation pre body before) := by
  cases history <;> simp_all [boundActivationSyntax]

def boundBodySyntax : SourceOperation α → Option (RuntimeActivation × List (Goose.Core.VarId × Value) × Block)
  | .boundActivationBody activation pre body => some (activation, pre, body)
  | _ => none

theorem body_statements_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome)
    (sourceFuel : Nat) (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (scope : Nat) (statements : List Stmt) (tail : Option Expr) (ready : ExecutionState)
    (fuelEq : fuel = sourceFuel + 1)
    (operationEq : boundBodySyntax operation = some (activation, pre, .mk scope statements tail))
    (bound : bindAll activation.act before.nextScope pre
      (Goose.Proofs.ConstructionGhostResultScope.resultScopeStart activation scope before) = .ok () ready) :
    SourceHistory config sourceFuel (path ++ [0])
      (.statements { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements) ready
      (execStmts sourceFuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements ready) := by
  cases history <;> simp_all [boundBodySyntax]

def statementsSyntax : SourceOperation α → Option (RuntimeActivation × List Stmt)
  | .statements environment statements => some (environment, statements)
  | _ => none

theorem statements_head_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome)
    (sourceFuel : Nat) (environment : RuntimeActivation) (statement : Stmt) (rest : List Stmt)
    (fuelEq : fuel = sourceFuel + 1)
    (operationEq : statementsSyntax operation = some (environment, statement :: rest)) :
    SourceHistory config sourceFuel (path ++ [0]) (.statement environment statement) before
      (execStmt sourceFuel config environment statement before) := by
  cases history <;> simp_all [statementsSyntax]
  case next =>
    rename_i child
    have actual := child.sound
    simp only [execute] at actual
    rw [actual]
    exact child

theorem statements_tail_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome)
    (sourceFuel : Nat) (environment : RuntimeActivation) (statement : Stmt) (rest : List Stmt)
    (value : Value) (middle : ExecutionState) (fuelEq : fuel = sourceFuel + 1)
    (operationEq : statementsSyntax operation = some (environment, statement :: rest))
    (headResult : execStmt sourceFuel config environment statement before = .ok (.normal value) middle) :
    SourceHistory config sourceFuel (path ++ [1]) (.statements environment rest) middle
      (execStmts sourceFuel config environment rest middle) := by
  cases history <;> simp_all [statementsSyntax]
  case next =>
    rename_i tail child
    have actual := child.sound
    simp only [execute] at actual
    apply tail value middle
    rw [← actual]
    exact headResult

#print axioms statements_tail_history
#print axioms statements_head_history
#print axioms body_statements_history
#print axioms activation_body_history
#print axioms call_activation_history
end Goose.Proofs.ConstructionGhostCallHistoryInversion
