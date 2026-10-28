import Goose.Proofs.ConstructionGhostBlockProducerTransition
import Goose.Proofs.ConstructionGhostResultScopeCore
import Goose.Proofs.ConstructionGhostInvocationVisitEvents
import Goose.Proofs.ConstructionGhostStatementEvents

namespace Goose.Proofs.ConstructionGhostResultBlockEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionGhostResultScope
open Goose.Proofs.ConstructionGhostActivationResultEvents Goose.Proofs.ConstructionGhostStatements
open Goose.Proofs.ConstructionGhostStatementEvents Goose.Proofs.ConstructionGhostInvocationVisitEvents
open Goose.Proofs.ConstructionGhostBlockProducerTransition Goose.Proofs.ConstructionGhostBlockValueChannels

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

theorem resultBlock_statementReplay (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (scope : Nat) (statements : List Stmt) (tail : Option Expr) (before : ExecutionState) :
    ∃ outcome visits,
      StatementReplay config { environment with scopes := (scope, before.nextScope) :: environment.scopes }
        fuel 0 statements (resultScopeStart environment scope before) outcome visits ∧
      execResultBlock (fuel + 2) config environment channels (.mk scope statements tail) before =
        withScope environment scope before.nextScope (fun _ => resultScopeContinuation channels tail
          (fun expression => evalProduce fuel config
            { environment with scopes := (scope, before.nextScope) :: environment.scopes } channels expression) outcome)
          (resultScopeStart environment scope before) := by
  have bound : bindAll environment.act before.nextScope [] (resultScopeStart environment scope before) =
      .ok () (resultScopeStart environment scope before) := by simp [bindAll, bind, pure]
  obtain ⟨outcome, visits, replay, execution⟩ := execResultScope_boundReplay fuel config environment [] channels scope statements tail
    (fun environment expression => evalProduce fuel config environment channels expression) before
    (resultScopeStart environment scope before) bound
  refine ⟨outcome, visits, replay, ?_⟩
  simpa [execResultBlock, execResultBlockWith] using execution

theorem resultBlock_replayPrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (scope : Nat) (statements : List Stmt) (tail : Option Expr) (before : ExecutionState)
    (outcome : ExecutionStep Flow) (visits : List StatementInvocation) (visit : StatementInvocation)
    (replay : StatementReplay config { environment with scopes := (scope, before.nextScope) :: environment.scopes }
      fuel 0 statements (resultScopeStart environment scope before) outcome visits) (member : visit ∈ visits) :
    EventPrefix (Goose.Proofs.Exit.stepState visit.outcome).construction.events
      (Goose.Proofs.Exit.stepState (execResultBlock (fuel + 2) config environment channels (.mk scope statements tail) before)).construction.events := by
  obtain ⟨other, otherVisits, otherReplay, execution⟩ := resultBlock_statementReplay fuel config environment channels scope statements tail before
  have same : other = outcome := otherReplay.sound.symm.trans replay.sound
  subst other
  rw [execution]
  let action := fun expression => evalProduce fuel config
    { environment with scopes := (scope, before.nextScope) :: environment.scopes } channels expression
  have preserved : ∀ expression, PreservesConstructionInvariant
      (PrefixInvariant (Goose.Proofs.Exit.stepState outcome).construction.events) (action expression) := by
    intro expression
    exact (evaluation_preservesConstructionInvariant fuel config).produce _ channels expression
  have continuation := resultScopeContinuation_resultPrefix channels tail action outcome preserved
  have scopePrefix := withScope_resultPrefix environment scope before.nextScope (fun _ =>
    resultScopeContinuation channels tail action outcome) (resultScopeStart environment scope before)
  have visitPrefix := invocationEvents_visitPrefix (statementReplay_invocationEvents replay) (statementInvocation visit)
    (List.mem_map.mpr ⟨visit, member, rfl⟩)
  exact eventPrefix_trans _ _ _ visitPrefix (eventPrefix_trans _ _ _ continuation scopePrefix)

theorem resultBlock_tailPrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (scope : Nat) (statements : List Stmt) (expression : Expr) (before ready : ExecutionState)
    (value : Value)
    (body : execStmts fuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes }
      statements (resultScopeStart environment scope before) = .ok (.normal value) ready) :
    EventPrefix (Goose.Proofs.Exit.stepState (evalProduce fuel config
      { environment with scopes := (scope, before.nextScope) :: environment.scopes } channels expression ready)).construction.events
      (Goose.Proofs.Exit.stepState (execResultBlock (fuel + 2) config environment channels (.mk scope statements (some expression)) before)).construction.events := by
  obtain ⟨outcome, visits, replay, execution⟩ := resultBlock_statementReplay fuel config environment channels scope statements (some expression) before
  have same := replay.sound.symm.trans body
  subst outcome
  rw [execution]
  let action : EvalM (Flow × List Carrier) := fun _ => resultScopeContinuation channels (some expression)
    (fun operand => evalProduce fuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes } channels operand)
    (.ok (.normal value) ready)
  have kept := withScope_resultPrefix environment scope before.nextScope action (resultScopeStart environment scope before)
  have sameEvents : (Goose.Proofs.Exit.stepState (action (resultScopeStart environment scope before))).construction.events =
      (Goose.Proofs.Exit.stepState (evalProduce fuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes }
        channels expression ready)).construction.events := by
    simp only [action, resultScopeContinuation, bind]
    cases evalProduce fuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes } channels expression ready <;> rfl
  rw [sameEvents] at kept
  exact kept

theorem blockValue_bodyVisitPrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr) (origin : Goose.Core.OriginId)
    (before channelsReady plannedReady : ExecutionState) (types : List Ty) (channels planned : List Channel)
    (outcome : ExecutionStep Flow) (visits : List StatementInvocation) (visit : StatementInvocation)
    (typesFound : blockResultTypes? (max (fuel + 3) (blockQueryBudget (.mk scope statements tail)))
      ⟨config.module, environment.vars⟩ (.mk scope statements tail) = some types)
    (channelsPrepared : channelsFor config.layout environment.act
      (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before = .ok channels channelsReady)
    (producerPrepared : prepareBlockProducerChannels channels origin channelsReady = .ok planned plannedReady)
    (replay : StatementReplay config
      { environment with scopes := (scope, (blockProducerStart environment planned plannedReady).nextScope) :: environment.scopes }
      fuel 0 statements (resultScopeStart environment scope (blockProducerStart environment planned plannedReady)) outcome visits)
    (member : visit ∈ visits) :
    EventPrefix (Goose.Proofs.Exit.stepState visit.outcome).construction.events
      (Goose.Proofs.Exit.stepState (evalValue (fuel + 4) config environment (.blockE (.mk scope statements tail) origin) before)).construction.events := by
  have bodyPrefix := resultBlock_replayPrefix fuel config environment planned scope statements tail
    (blockProducerStart environment planned plannedReady) outcome visits visit replay member
  have producerPrefix := blockProducer_resultBlockPrefix (fuel + 2) config environment (.mk scope statements tail) origin
    channels planned channelsReady plannedReady producerPrepared
  have valuePrefix := blockValue_producerPrefix (fuel + 3) config environment (.mk scope statements tail) origin
    before channelsReady types channels typesFound channelsPrepared
  exact eventPrefix_trans _ _ _ bodyPrefix (eventPrefix_trans _ _ _ producerPrefix valuePrefix)

theorem blockValue_tailProducerPrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (scope : Nat) (statements : List Stmt) (expression : Expr) (origin : Goose.Core.OriginId)
    (before channelsReady plannedReady bodyReady : ExecutionState) (types : List Ty) (channels planned : List Channel) (value : Value)
    (typesFound : blockResultTypes? (max (fuel + 3) (blockQueryBudget (.mk scope statements (some expression))))
      ⟨config.module, environment.vars⟩ (.mk scope statements (some expression)) = some types)
    (channelsPrepared : channelsFor config.layout environment.act
      (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before = .ok channels channelsReady)
    (producerPrepared : prepareBlockProducerChannels channels origin channelsReady = .ok planned plannedReady)
    (body : execStmts fuel config
      { environment with scopes := (scope, (blockProducerStart environment planned plannedReady).nextScope) :: environment.scopes }
      statements (resultScopeStart environment scope (blockProducerStart environment planned plannedReady)) = .ok (.normal value) bodyReady) :
    EventPrefix (Goose.Proofs.Exit.stepState (evalProduce fuel config
      { environment with scopes := (scope, (blockProducerStart environment planned plannedReady).nextScope) :: environment.scopes }
      planned expression bodyReady)).construction.events
      (Goose.Proofs.Exit.stepState (evalValue (fuel + 4) config environment (.blockE (.mk scope statements (some expression)) origin) before)).construction.events := by
  have tailPrefix := resultBlock_tailPrefix fuel config environment planned scope statements expression
    (blockProducerStart environment planned plannedReady) bodyReady value body
  have producerPrefix := blockProducer_resultBlockPrefix (fuel + 2) config environment (.mk scope statements (some expression)) origin
    channels planned channelsReady plannedReady producerPrepared
  have valuePrefix := blockValue_producerPrefix (fuel + 3) config environment (.mk scope statements (some expression)) origin
    before channelsReady types channels typesFound channelsPrepared
  exact eventPrefix_trans _ _ _ tailPrefix (eventPrefix_trans _ _ _ producerPrefix valuePrefix)

#print axioms blockValue_bodyVisitPrefix
#print axioms blockValue_tailProducerPrefix
#print axioms resultBlock_tailPrefix
#print axioms resultBlock_statementReplay
#print axioms resultBlock_replayPrefix
end Goose.Proofs.ConstructionGhostResultBlockEvents
