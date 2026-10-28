import Goose.Proofs.ConstructionGhostModuleResultEvents
import Goose.Proofs.ConstructionGhostDeclarationNestedCall

namespace Goose.Proofs.ConstructionGhostCallResultEvents
open Goose.Construct Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostActivationResultEvents Goose.Proofs.ConstructionGhostActivationEvents
open Goose.Proofs.ConstructionGhostModuleResultEvents Goose.Proofs.ConstructionGhostResultScope
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostStatementEvents
open Goose.Proofs.ConstructionGhostInvocationVisitEvents Goose.Proofs.ConstructionGhostDeclarationReplay
open Goose.Proofs.ConstructionGhostDeclaration Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostDeclarationOnce Goose.Proofs.ConstructionGhostDeclarationSelection
open Goose.Proofs.ConstructionGhostDeclarationFallback

theorem call_visitPrefix (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (implementation : Impl) (pre : List (Goose.Core.VarId × Value)) (scope : Nat)
    (statements : List Stmt) (tail : Option Expr) (activated ready : ExecutionState)
    (channels : List Channel) (origin : Goose.Core.OriginId) (callResult : ExecutionStep (List Carrier))
    (outcome : ExecutionStep Flow) (visits : List StatementInvocation) (visit : StatementInvocation)
    (found : config.module.impls[activation.implementation]? = some implementation)
    (body : implementation.body = .mk scope statements tail)
    (replay : StatementReplay config { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
      fuel 0 statements ready outcome visits)
    (member : visit ∈ visits)
    (execution : execActivationBody (fuel + 1) config activation pre implementation.body activated =
      activationBodyFinish (withScope activation scope activated.nextScope (fun _ =>
        resultScopeContinuation activation.channels tail
          (fun expression => withCompletionChannels activation.channels (expressionOrigin expression)
            (fun channels => evalProduce fuel config
              { activation with scopes := (scope, activated.nextScope) :: activation.scopes } channels expression)) outcome)
        (resultScopeStart activation scope activated)))
    (call : callResult = ((enterActivation (fuel + 2) config activation pre implementation.body origin >>= fun carriers =>
      deliverCarriers (fuel + 2) config.layout channels carriers origin) activated)) :
    EventPrefix (Goose.Proofs.Exit.stepState visit.outcome).construction.events
      (Goose.Proofs.Exit.stepState callResult).construction.events := by
  have kept := call_resultPrefix fuel config activation implementation pre scope statements tail activated channels origin
    callResult outcome found body execution call
  have visitsKept := invocationEvents_visitPrefix (statementReplay_invocationEvents replay) (statementInvocation visit)
    (List.mem_map.mpr ⟨visit, member, rfl⟩)
  exact eventPrefix_trans _ _ _ visitsKept kept

theorem declarationClassification_resultPrefix (config : EvalConfig) (environment : RuntimeActivation)
    (visit : StatementInvocation) (sourceFuel : Nat) (localVar : Goose.Core.VarId) (expression : Expr)
    (origin : Goose.Core.OriginId) (finalEvents : List Goose.Core.ConstructionEvent)
    (classification : VisitClassification config environment visit sourceFuel localVar expression origin)
    (visitPrefix : EventPrefix (Goose.Proofs.Exit.stepState visit.outcome).construction.events finalEvents) :
    (∃ destination ready, DeclarationOccurrence sourceFuel config environment localVar expression origin visit.before destination ready ∧
      (∀ other otherReady, DeclarationOccurrence sourceFuel config environment localVar expression origin visit.before other otherReady →
        destination = other ∧ ready = otherReady) ∧
      match destination with
      | none => SourceHistory config sourceFuel [environment.act, visit.ordinal, 0] (.value environment expression) ready
          (evalValue sourceFuel config environment expression ready) ∧
          EventPrefix (Goose.Proofs.Exit.stepState (evalValue sourceFuel config environment expression ready)).construction.events finalEvents
      | some destination => SourceHistory config sourceFuel [environment.act, visit.ordinal, 0] (.builder environment destination expression) ready
          (buildExpr sourceFuel config environment destination expression ready) ∧
          EventPrefix (Goose.Proofs.Exit.stepState (buildExpr sourceFuel config environment destination expression ready)).construction.events finalEvents) ∨
    ((∃ terminal : DeclarationTerminal, visit.outcome = terminal.step) ∧
      ¬ ∃ destination ready, DeclarationOccurrence sourceFuel config environment localVar expression origin visit.before destination ready) := by
  rcases classification with ⟨destination, ready, occurrence, unique, child⟩ | terminal
  · left
    refine ⟨destination, ready, occurrence, unique, ?_⟩
    cases destination with
    | none => exact ⟨child.1, eventPrefix_trans _ _ _ child.2 visitPrefix⟩
    | some destination => exact ⟨child.1, eventPrefix_trans _ _ _ child.2 visitPrefix⟩
  · exact Or.inr terminal

#print axioms declarationClassification_resultPrefix
#print axioms call_visitPrefix
end Goose.Proofs.ConstructionGhostCallResultEvents
