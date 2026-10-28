import Goose.Proofs.ConstructionGhostResultBlockEvents
import Goose.Proofs.ConstructionGhostStatementPaths
import Goose.Proofs.ConstructionGhostSourceFuel

namespace Goose.Proofs.ConstructionGhostResultBlockHistory
open Goose.Construct Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostStatementPaths
open Goose.Proofs.ConstructionGhostResultScope Goose.Proofs.ConstructionGhostResultBlockEvents
open Goose.Proofs.ConstructionGhostBlockProducerTransition Goose.Proofs.ConstructionGhostBlockValueChannels

theorem resultBlock_fuelHistories (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (path : List Nat) (before : ExecutionState)
    (bodySupported : ∀ scopedEnvironment, FuelSupport config fuel (.statements scopedEnvironment statements))
    (tailSupported : ∀ scopedEnvironment expression, tail = some expression → FuelSupport config fuel (.producerWith scopedEnvironment channels expression)) :
    let scopedEnvironment := { environment with scopes := (scope, before.nextScope) :: environment.scopes }
    let bodyBefore := resultScopeStart environment scope before
    ∃ outcome visits,
      StatementReplay config scopedEnvironment fuel 0 statements bodyBefore outcome visits ∧
      (visits.map StatementInvocation.ordinal).Nodup ∧
      (∀ visit ∈ visits, ∃ suffix, StatementPath 0 suffix visit.ordinal ∧
        SourceHistory config visit.fuel ((path ++ [0]) ++ suffix) (.statement scopedEnvironment visit.statement) visit.before visit.outcome ∧
        EventPrefix (Goose.Proofs.Exit.stepState visit.outcome).construction.events
          (Goose.Proofs.Exit.stepState (execResultBlock (fuel + 2) config environment channels (.mk scope statements tail) before)).construction.events) ∧
      (∀ expression value ready, tail = some expression → outcome = .ok (.normal value) ready →
        SourceHistory config fuel (path ++ [1]) (.producerWith scopedEnvironment channels expression) ready
          (evalProduce fuel config scopedEnvironment channels expression ready) ∧
        EventPrefix (Goose.Proofs.Exit.stepState (evalProduce fuel config scopedEnvironment channels expression ready)).construction.events
          (Goose.Proofs.Exit.stepState (execResultBlock (fuel + 2) config environment channels (.mk scope statements tail) before)).construction.events) := by
  obtain ⟨outcome, visits, replay, execution⟩ := resultBlock_statementReplay fuel config environment channels scope statements tail before
  have bodyHistory := fuelHistory_exists fuel config
    (.statements { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements) (path ++ [0])
    (resultScopeStart environment scope before) (bodySupported _)
  simp only [execute] at bodyHistory
  rw [replay.sound] at bodyHistory
  have paths := statementReplay_sourcePaths replay (path ++ [0]) bodyHistory
  refine ⟨outcome, visits, replay, replay.once, ?_, ?_⟩
  · intro visit member
    obtain ⟨suffix, suffixPath, child⟩ := paths visit member
    exact ⟨suffix, suffixPath, child, resultBlock_replayPrefix fuel config environment channels scope statements tail before outcome visits visit replay member⟩
  · intro expression value ready tailEq outcomeEq
    subst tail
    have body : execStmts fuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes }
        statements (resultScopeStart environment scope before) = .ok (.normal value) ready := replay.sound.trans outcomeEq
    exact ⟨fuelHistory_exists fuel config _ (path ++ [1]) ready (tailSupported _ expression rfl),
      resultBlock_tailPrefix fuel config environment channels scope statements expression before ready value body⟩

theorem blockValue_fuelHistories (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr) (origin : Goose.Core.OriginId)
    (path : List Nat) (before channelsReady plannedReady : ExecutionState) (types : List Ty) (channels planned : List Channel)
    (typesFound : blockResultTypes? (max (fuel + 3) (blockQueryBudget (.mk scope statements tail)))
      ⟨config.module, environment.vars⟩ (.mk scope statements tail) = some types)
    (channelsPrepared : channelsFor config.layout environment.act
      (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before = .ok channels channelsReady)
    (producerPrepared : prepareBlockProducerChannels channels origin channelsReady = .ok planned plannedReady)
    (bodySupported : ∀ scopedEnvironment, FuelSupport config fuel (.statements scopedEnvironment statements))
    (tailSupported : ∀ scopedEnvironment expression, tail = some expression → FuelSupport config fuel (.producerWith scopedEnvironment planned expression)) :
    let blockBefore := blockProducerStart environment planned plannedReady
    let scopedEnvironment := { environment with scopes := (scope, blockBefore.nextScope) :: environment.scopes }
    let bodyBefore := resultScopeStart environment scope blockBefore
    ∃ outcome visits,
      StatementReplay config scopedEnvironment fuel 0 statements bodyBefore outcome visits ∧
      (visits.map StatementInvocation.ordinal).Nodup ∧
      (∀ visit ∈ visits, ∃ suffix, StatementPath 0 suffix visit.ordinal ∧
        SourceHistory config visit.fuel ((path ++ [0]) ++ suffix) (.statement scopedEnvironment visit.statement) visit.before visit.outcome ∧
        EventPrefix (Goose.Proofs.Exit.stepState visit.outcome).construction.events
          (Goose.Proofs.Exit.stepState (evalValue (fuel + 4) config environment (.blockE (.mk scope statements tail) origin) before)).construction.events) ∧
      (∀ expression value ready, tail = some expression → outcome = .ok (.normal value) ready →
        SourceHistory config fuel (path ++ [1]) (.producerWith scopedEnvironment planned expression) ready
          (evalProduce fuel config scopedEnvironment planned expression ready) ∧
        EventPrefix (Goose.Proofs.Exit.stepState (evalProduce fuel config scopedEnvironment planned expression ready)).construction.events
          (Goose.Proofs.Exit.stepState (evalValue (fuel + 4) config environment (.blockE (.mk scope statements tail) origin) before)).construction.events) := by
  obtain ⟨outcome, visits, replay, once, children, tailChild⟩ := resultBlock_fuelHistories fuel config environment planned scope statements tail
    path (blockProducerStart environment planned plannedReady) bodySupported tailSupported
  have producerPrefix := blockProducer_resultBlockPrefix (fuel + 2) config environment (.mk scope statements tail) origin
    channels planned channelsReady plannedReady producerPrepared
  have valuePrefix := blockValue_producerPrefix (fuel + 3) config environment (.mk scope statements tail) origin
    before channelsReady types channels typesFound channelsPrepared
  have parentPrefix := eventPrefix_trans _ _ _ producerPrefix valuePrefix
  refine ⟨outcome, visits, replay, once, ?_, ?_⟩
  · intro visit member
    obtain ⟨suffix, suffixPath, child, kept⟩ := children visit member
    exact ⟨suffix, suffixPath, child, eventPrefix_trans _ _ _ kept parentPrefix⟩
  · intro expression value ready tailEq outcomeEq
    obtain ⟨child, kept⟩ := tailChild expression value ready tailEq outcomeEq
    exact ⟨child, eventPrefix_trans _ _ _ kept parentPrefix⟩

#print axioms blockValue_fuelHistories
#print axioms resultBlock_fuelHistories
end Goose.Proofs.ConstructionGhostResultBlockHistory
