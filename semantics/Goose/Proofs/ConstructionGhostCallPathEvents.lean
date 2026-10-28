import Goose.Proofs.ConstructionGhostCallResultEvents
import Goose.Proofs.ConstructionGhostCallStatementPaths

namespace Goose.Proofs.ConstructionGhostCallPathEvents
open Goose.Construct Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostStatements
open Goose.Proofs.ConstructionGhostDeclarationNestedCall Goose.Proofs.ConstructionGhostCallHistoryInversion
open Goose.Proofs.ConstructionGhostCallStatementPaths Goose.Proofs.ConstructionGhostStatementPaths
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostCallActivation
open Goose.Proofs.ConstructionGhostCallResultEvents Goose.Proofs.ConstructionGhostResultScope

theorem call_statementPathEvents (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (contextId : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (before lookupReady argumentsReady valuesReady activationReady boundReady : ExecutionState)
    (id : Goose.Core.ImplId) (implementation : Impl) (callableChannels refreshed : List Channel) (values : List Value)
    (history : SourceHistory config (fuel + 3) path (.channelCall environment contextId arguments channels origin) before
      (invokeCall (fuel + 3) config environment contextId arguments channels origin before))
    (lookup : getImplementation config contextId before = .ok (id, implementation) lookupReady)
    (implemented : config.module.impls[id]? = some implementation) (arity : channels.length = implementation.results.size)
    (prepared : prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels argumentsReady)
    (argumentsResult : evalArguments (fuel + 2) config environment implementation.vars implementation.params.toList arguments argumentsReady = .ok values valuesReady)
    (refresh : refreshCallableChannels callableChannels origin valuesReady = .ok refreshed activationReady)
    (depth : activationReady.activations.length < Goose.Core.maxCallDepth)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr) (body : implementation.body = .mk scope statements tail)
    (closed : ClosedModuleWithTails config) (statementSyntax : ∀ statement ∈ statements, StatementSyntax config statement)
    (bound : let activation : RuntimeActivation := ⟨id, activationReady.nextAct, implementation.vars, [], refreshed⟩
      let activated := { activationReady with nextAct := activationReady.nextAct + 1, activations := activation :: activationReady.activations }
      bindAll activation.act activated.nextScope
        ((implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value))
        (resultScopeStart activation scope activated) = .ok () boundReady) :
    let activation : RuntimeActivation := ⟨id, activationReady.nextAct, implementation.vars, [], refreshed⟩
    let activated := { activationReady with nextAct := activationReady.nextAct + 1, activations := activation :: activationReady.activations }
    let scopedEnvironment := { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
    ∃ outcome visits,
      StatementReplay config scopedEnvironment fuel 0 statements boundReady outcome visits ∧
      (visits.map StatementInvocation.ordinal).Nodup ∧
      ∀ visit ∈ visits, ∃ suffix, StatementPath 0 suffix visit.ordinal ∧
        SourceHistory config visit.fuel (((path ++ [1]) ++ [0] ++ [0]) ++ suffix)
          (.statement scopedEnvironment visit.statement) visit.before visit.outcome ∧
        EventPrefix (Goose.Proofs.Exit.stepState visit.outcome).construction.events
          (Goose.Proofs.Exit.stepState (invokeCall (fuel + 3) config environment contextId arguments channels origin before)).construction.events := by
  have activationHistory := call_activation_history history (fuel + 2) environment contextId arguments channels origin
    lookupReady argumentsReady valuesReady activationReady id implementation callableChannels refreshed values
    rfl rfl lookup arity prepared argumentsResult refresh depth
  have bodyHistory := activation_body_history activationHistory (fuel + 1)
    ⟨id, activationReady.nextAct, implementation.vars, [], refreshed⟩
    ((implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value))
    implementation.body origin implementation rfl rfl implemented
  rw [body] at bodyHistory
  have statementsHistory := body_statements_history bodyHistory fuel
    ⟨id, activationReady.nextAct, implementation.vars, [], refreshed⟩
    ((implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value))
    scope statements tail boundReady rfl rfl bound
  obtain ⟨outcome, visits, replay, once, bodyExecution, classification, callExecution⟩ :=
    call_declarationVisits fuel config environment contextId arguments channels origin before lookupReady argumentsReady
      valuesReady activationReady boundReady id implementation callableChannels refreshed values lookup arity prepared argumentsResult
      refresh depth scope statements tail body closed statementSyntax bound
  rw [replay.sound] at statementsHistory
  have paths := statementReplay_sourcePaths replay (((path ++ [1]) ++ [0]) ++ [0]) statementsHistory
  refine ⟨outcome, visits, replay, once, ?_⟩
  intro visit member
  obtain ⟨suffix, suffixPath, child⟩ := paths visit member
  refine ⟨suffix, suffixPath, child, ?_⟩
  exact call_visitPrefix fuel config ⟨id, activationReady.nextAct, implementation.vars, [], refreshed⟩ implementation
    ((implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)) scope statements tail
    { activationReady with nextAct := activationReady.nextAct + 1, activations :=
      (⟨id, activationReady.nextAct, implementation.vars, [], refreshed⟩ : RuntimeActivation) :: activationReady.activations }
    boundReady channels origin (invokeCall (fuel + 3) config environment contextId arguments channels origin before)
    outcome visits visit implemented body replay member bodyExecution callExecution

#print axioms call_statementPathEvents
end Goose.Proofs.ConstructionGhostCallPathEvents
