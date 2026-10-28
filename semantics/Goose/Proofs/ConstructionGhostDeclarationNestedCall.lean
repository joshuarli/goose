import Goose.Proofs.ConstructionGhostDeclarationReplay
import Goose.Proofs.ConstructionGhostActivationEvents
import Goose.Proofs.ConstructionGhostCallActivation

namespace Goose.Proofs.ConstructionGhostDeclarationNestedCall
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostStatements
open Goose.Proofs.ConstructionGhostDeclarationReplay Goose.Proofs.ConstructionGhostActivationEvents
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostCallActivation
open Goose.Proofs.ConstructionGhostResultScope

theorem call_declarationVisits (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (contextId : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (before lookupReady argumentsReady valuesReady activationReady boundReady : ExecutionState)
    (id : Goose.Core.ImplId) (implementation : Impl) (callableChannels refreshed : List Channel) (values : List Value)
    (lookup : getImplementation config contextId before = .ok (id, implementation) lookupReady)
    (arity : channels.length = implementation.results.size)
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
    let pre := (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
    let scopedEnvironment := { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
    ∃ outcome visits,
      StatementReplay config scopedEnvironment fuel 0 statements boundReady outcome visits ∧
      (visits.map StatementInvocation.ordinal).Nodup ∧
      execActivationBody (fuel + 1) config activation pre implementation.body activated =
        activationBodyFinish (withScope activation scope activated.nextScope (fun _ =>
          resultScopeContinuation activation.channels tail
            (fun expression => withCompletionChannels activation.channels (expressionOrigin expression)
              (fun channels => evalProduce fuel config scopedEnvironment channels expression)) outcome)
          (resultScopeStart activation scope activated)) ∧
      (∀ visit ∈ visits, ∀ sourceFuel localVar expression statementOrigin,
        visit.fuel = sourceFuel + 1 → visit.statement = .letS localVar expression statementOrigin →
        VisitClassification config scopedEnvironment visit sourceFuel localVar expression statementOrigin) ∧
      invokeCall (fuel + 3) config environment contextId arguments channels origin before =
        ((enterActivation (fuel + 2) config activation pre implementation.body origin >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout channels carriers origin) activated) := by
  dsimp only at bound ⊢
  have supported : ∀ sourceFuel localVar expression statementOrigin, .letS localVar expression statementOrigin ∈ statements →
      FuelSupport config sourceFuel
        (.value { (⟨id, activationReady.nextAct, implementation.vars, [], refreshed⟩ : RuntimeActivation) with
          scopes := [(scope, activationReady.nextScope)] } expression) := by
    intro sourceFuel localVar expression statementOrigin member
    have derivation := statementSyntax (.letS localVar expression statementOrigin) member
    cases derivation with
    | declaration _ _ _ value _ => exact (syntaxFuel_existsWithTails sourceFuel config closed).value _ expression value
  obtain ⟨outcome, visits, chunks, replay, ordered, once, aligned, finalEq, execution, fixed⟩ :=
    activationBody_fixedSourceEvents fuel config ⟨id, activationReady.nextAct, implementation.vars, [], refreshed⟩
      ((implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value))
      scope statements tail ({ activationReady with nextAct := activationReady.nextAct + 1, activations :=
        (⟨id, activationReady.nextAct, implementation.vars, [], refreshed⟩ : RuntimeActivation) :: activationReady.activations })
      boundReady bound supported
  obtain ⟨argumentsOutcome, argumentVisits, argumentReplay, argumentOrdered, argumentOnce, callExecution⟩ :=
    invokeCall_argumentReplay (fuel + 2) config environment contextId arguments channels origin before lookupReady argumentsReady
      id implementation callableChannels lookup arity prepared
  have actual := argumentReplay.sound
  rw [argumentsResult] at actual
  subst argumentsOutcome
  refine ⟨outcome, visits, replay, once, ?_, ?_, ?_⟩
  · rw [body]
    exact execution
  · intro visit member sourceFuel localVar expression statementOrigin visitFuel visitStatement
    have inMapped : visit.statement ∈ visits.map StatementInvocation.statement := List.mem_map_of_mem member
    rw [ordered] at inMapped
    exact declaration_visit_classification replay visit member sourceFuel localVar expression statementOrigin visitFuel visitStatement
      closed (statementSyntax visit.statement (List.mem_of_mem_take inMapped))
  · rw [callExecution]
    exact callAfterArguments_activation (fuel + 2) config id implementation channels callableChannels refreshed origin values
      valuesReady activationReady refresh depth

#print axioms call_declarationVisits
end Goose.Proofs.ConstructionGhostDeclarationNestedCall
