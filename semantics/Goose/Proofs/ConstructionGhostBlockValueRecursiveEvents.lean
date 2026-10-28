import Goose.Proofs.ConstructionGhostBlockValueHistory
import Goose.Proofs.ConstructionGhostResultBlockEvents
import Goose.Proofs.ConstructionGhostStatementPaths

namespace Goose.Proofs.ConstructionGhostBlockValueRecursiveEvents
open Goose.Construct Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostStatements
open Goose.Proofs.ConstructionGhostBlockValueHistory Goose.Proofs.ConstructionGhostStatementPaths
open Goose.Proofs.ConstructionGhostBlockProducerTransition Goose.Proofs.ConstructionGhostResultScope
open Goose.Proofs.ConstructionGhostResultBlockEvents

theorem blockValue_recursiveHistories (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr) (origin : Goose.Core.OriginId) (path : List Nat)
    (before channelsReady plannedReady : ExecutionState) (types : List Ty) (channels planned : List Channel)
    (history : SourceHistory config (fuel + 4) path (.value environment (.blockE (.mk scope statements tail) origin)) before
      (evalValue (fuel + 4) config environment (.blockE (.mk scope statements tail) origin) before))
    (typesFound : blockResultTypes? (max (fuel + 3) (blockQueryBudget (.mk scope statements tail)))
      ⟨config.module, environment.vars⟩ (.mk scope statements tail) = some types)
    (channelsPrepared : channelsFor config.layout environment.act
      (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before = .ok channels channelsReady)
    (producerPrepared : prepareBlockProducerChannels channels origin channelsReady = .ok planned plannedReady) :
    let blockBefore := blockProducerStart environment planned plannedReady
    let scopedEnvironment := { environment with scopes := (scope, blockBefore.nextScope) :: environment.scopes }
    let bodyBefore := resultScopeStart environment scope blockBefore
    ∃ outcome visits,
      StatementReplay config scopedEnvironment fuel 0 statements bodyBefore outcome visits ∧
      (visits.map StatementInvocation.ordinal).Nodup ∧
      (∀ visit ∈ visits, ∃ suffix, StatementPath 0 suffix visit.ordinal ∧
        SourceHistory config visit.fuel (((((path ++ [0]) ++ [0]) ++ [0]) ++ [0]) ++ suffix)
          (.statement scopedEnvironment visit.statement) visit.before visit.outcome ∧
        EventPrefix (Goose.Proofs.Exit.stepState visit.outcome).construction.events
          (Goose.Proofs.Exit.stepState (evalValue (fuel + 4) config environment (.blockE (.mk scope statements tail) origin) before)).construction.events) ∧
      (∀ expression value ready, tail = some expression → outcome = .ok (.normal value) ready →
        SourceHistory config fuel ((((path ++ [0]) ++ [0]) ++ [0]) ++ [1]) (.producerWith scopedEnvironment planned expression) ready
          (evalProduce fuel config scopedEnvironment planned expression ready) ∧
        EventPrefix (Goose.Proofs.Exit.stepState (evalProduce fuel config scopedEnvironment planned expression ready)).construction.events
          (Goose.Proofs.Exit.stepState (evalValue (fuel + 4) config environment (.blockE (.mk scope statements tail) origin) before)).construction.events) := by
  have producerHistory := blockValue_producer_history history (fuel + 3) environment (.mk scope statements tail) origin types channels channelsReady
    rfl rfl typesFound channelsPrepared
  have resultHistory := blockProducer_resultBlock_history producerHistory (fuel + 2) environment channels planned (.mk scope statements tail) origin plannedReady
    rfl rfl producerPrepared
  have scopeHistory := resultBlock_with_history resultHistory (fuel + 1) environment planned (.mk scope statements tail) rfl rfl
  let blockBefore := blockProducerStart environment planned plannedReady
  have bound : bindAll environment.act blockBefore.nextScope [] (resultScopeStart environment scope blockBefore) =
      .ok () (resultScopeStart environment scope blockBefore) := by simp [bindAll, bind, pure]
  have bodyHistory := resultBlock_body_history scopeHistory fuel environment [] planned scope statements tail
    (resultScopeStart environment scope blockBefore) rfl rfl bound
  obtain ⟨outcome, visits, replay, execution⟩ := resultBlock_statementReplay fuel config environment planned scope statements tail blockBefore
  rw [replay.sound] at bodyHistory
  have paths := statementReplay_sourcePaths replay ((((path ++ [0]) ++ [0]) ++ [0]) ++ [0]) bodyHistory
  refine ⟨outcome, visits, replay, replay.once, ?_, ?_⟩
  · intro visit member
    obtain ⟨suffix, suffixPath, child⟩ := paths visit member
    exact ⟨suffix, suffixPath, child, blockValue_bodyVisitPrefix fuel config environment scope statements tail origin
      before channelsReady plannedReady types channels planned outcome visits visit typesFound channelsPrepared producerPrepared replay member⟩
  · intro expression value ready tailEq outcomeEq
    subst tail
    have body : execStmts fuel config { environment with scopes := (scope, blockBefore.nextScope) :: environment.scopes }
        statements (resultScopeStart environment scope blockBefore) = .ok (.normal value) ready := replay.sound.trans outcomeEq
    have child := resultBlock_tail_history scopeHistory fuel environment [] planned scope statements expression
      (resultScopeStart environment scope blockBefore) ready value rfl rfl bound body
    exact ⟨child, blockValue_tailProducerPrefix fuel config environment scope statements expression origin
      before channelsReady plannedReady ready types channels planned value typesFound channelsPrepared producerPrepared body⟩

#print axioms blockValue_recursiveHistories
end Goose.Proofs.ConstructionGhostBlockValueRecursiveEvents
