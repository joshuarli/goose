import Goose.Proofs.ConstructionGhostFixedDeclarationEvents
import Goose.Proofs.ConstructionGhostResultScopeCore

namespace Goose.Proofs.ConstructionGhostActivationEvents
open Goose.Construct Goose.Proofs.ConstructionGhostStatements
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostResultScope Goose.Proofs.ConstructionGhostStatementEvents
open Goose.Proofs.ConstructionGhostFixedDeclarationEvents Goose.Proofs.ConstructionGhostInvocationEventChunks

def activationBodyFinish : ExecutionStep (Flow × List Carrier) → ExecutionStep (List Carrier)
  | .ok (.normal _, carriers) state => .ok carriers state
  | .ok _ state => .stop (.fault .flow) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem activationBody_fixedSourceEvents (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (before ready : ExecutionState)
    (bound : bindAll activation.act before.nextScope pre (resultScopeStart activation scope before) = .ok () ready)
    (supported : ∀ sourceFuel localVar expression origin, .letS localVar expression origin ∈ statements →
      FuelSupport config sourceFuel
        (.value { activation with scopes := (scope, before.nextScope) :: activation.scopes } expression)) :
    ∃ outcome visits chunks,
      StatementReplay config { activation with scopes := (scope, before.nextScope) :: activation.scopes }
        fuel 0 statements ready outcome visits ∧
      visits.map StatementInvocation.statement = statements.take visits.length ∧
      (visits.map StatementInvocation.ordinal).Nodup ∧ ChunksAlign (visits.map statementInvocation) chunks ∧
      (Goose.Proofs.Exit.stepState outcome).construction.events = ready.construction.events ++ chunks.flatten ∧
      execActivationBody (fuel + 1) config activation pre (.mk scope statements tail) before =
        activationBodyFinish (withScope activation scope before.nextScope (fun _ =>
          resultScopeContinuation activation.channels tail
            (fun expression => withCompletionChannels activation.channels (expressionOrigin expression)
              (fun channels => evalProduce fuel config
                { activation with scopes := (scope, before.nextScope) :: activation.scopes } channels expression)) outcome)
          (resultScopeStart activation scope before)) ∧
      ∀ visit ∈ visits, ∀ sourceFuel localVar expression origin descriptor root sourceReady,
        visit.fuel = sourceFuel + 1 → visit.statement = .letS localVar expression origin →
        activation.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = false →
        rootOf { activation with scopes := (scope, before.nextScope) :: activation.scopes } localVar visit.before = .ok root sourceReady →
        SourceHistory config sourceFuel [activation.act, visit.ordinal, 0]
          (.value { activation with scopes := (scope, before.nextScope) :: activation.scopes } expression) sourceReady
          (evalValue sourceFuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes } expression sourceReady) ∧
        (Goose.Proofs.Exit.stepState visit.outcome).construction.events =
          (Goose.Proofs.Exit.stepState
            (evalValue sourceFuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes } expression sourceReady)).construction.events := by
  obtain ⟨outcome, visits, replay, execution⟩ := execResultScope_boundReplay fuel config activation pre activation.channels
    scope statements tail (fun environment expression => withCompletionChannels activation.channels (expressionOrigin expression)
      (fun channels => evalProduce fuel config environment channels expression)) before ready bound
  obtain ⟨chunks, forest, ordered, once, aligned, finalEq⟩ := statementReplay_initializerEventChunks replay
  refine ⟨outcome, visits, chunks, replay, ordered, once, aligned, finalEq, ?_, statementReplay_fixedSourceEvents replay supported⟩
  simp only [execActivationBody, bind, execution, activationBodyFinish]
  cases result : withScope activation scope before.nextScope (fun _ =>
    resultScopeContinuation activation.channels tail
      (fun expression => withCompletionChannels activation.channels (expressionOrigin expression)
        (fun channels => evalProduce fuel config
          { activation with scopes := (scope, before.nextScope) :: activation.scopes } channels expression)) outcome)
    (resultScopeStart activation scope before) with
  | ok pair state => cases pair with | mk flow carriers => cases flow <;> simp [result, bind, pure, fault, EvalM.stop]
  | stop | escape | jump => simp [result]

#print axioms activationBody_fixedSourceEvents
end Goose.Proofs.ConstructionGhostActivationEvents
