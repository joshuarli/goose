import Goose.Proofs.ConstructionGhostBlockInitializers
import Goose.Proofs.ConstructionGhostInvocationEventChunks

namespace Goose.Proofs.ConstructionGhostStatementEvents
open Goose.Construct Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostBlockInitializers Goose.Proofs.ConstructionGhostBlock
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocationEvents
open Goose.Proofs.ConstructionGhostInvocationEventChunks

def statementInvocation (visit : StatementInvocation) : Invocation Stmt Flow :=
  ⟨visit.ordinal, visit.statement, visit.before, visit.outcome⟩

theorem statementReplay_invocationEvents
    (replay : StatementReplay config environment fuel offset statements before outcome visits) :
    InvocationEvents before.construction.events (visits.map statementInvocation)
      (Goose.Proofs.Exit.stepState outcome).construction.events := by
  induction replay with
  | timeout | done => exact .done _
  | @next fuel offset statement rest before middle value outcome visits head tail ih =>
      have segment := (evaluation_keepsEventPrefix fuel config).statement environment statement before
      rw [head] at segment
      exact .next ⟨offset, statement, before, .ok (.normal value) middle⟩ _ _ segment ih
  | @breaking fuel offset statement rest before after value head =>
      have segment := (evaluation_keepsEventPrefix fuel config).statement environment statement before
      rw [head] at segment
      exact .next ⟨offset, statement, before, .ok (Flow.breaking value) after⟩ [] _ segment (.done _)
  | @continuing fuel offset statement rest before after head =>
      have segment := (evaluation_keepsEventPrefix fuel config).statement environment statement before
      rw [head] at segment
      exact .next ⟨offset, statement, before, .ok Flow.continuing after⟩ [] _ segment (.done _)
  | @stopped fuel offset statement rest before after reason head =>
      have segment := (evaluation_keepsEventPrefix fuel config).statement environment statement before
      rw [head] at segment
      exact .next ⟨offset, statement, before, .stop reason after⟩ [] _ segment (.done _)
  | @escaped fuel offset statement rest before after address carriers head =>
      have segment := (evaluation_keepsEventPrefix fuel config).statement environment statement before
      rw [head] at segment
      exact .next ⟨offset, statement, before, .escape address carriers after⟩ [] _ segment (.done _)
  | @jumped fuel offset statement rest before after target kind head =>
      have segment := (evaluation_keepsEventPrefix fuel config).statement environment statement before
      rw [head] at segment
      exact .next ⟨offset, statement, before, .jump target kind after⟩ [] _ segment (.done _)

theorem statementReplay_initializerEventChunks
    (replay : StatementReplay config environment fuel offset statements before outcome visits) :
    ∃ chunks,
      FixedOrMaterializedInitializerForest config environment visits ∧
      visits.map StatementInvocation.statement = statements.take visits.length ∧
      (visits.map StatementInvocation.ordinal).Nodup ∧
      ChunksAlign (visits.map statementInvocation) chunks ∧
      (Goose.Proofs.Exit.stepState outcome).construction.events = before.construction.events ++ chunks.flatten := by
  obtain ⟨chunks, aligned, finalEq⟩ := invocationEvents_chunks (statementReplay_invocationEvents replay)
  exact ⟨chunks, statementReplay_initializerForest replay, replay.sourceOrder, replay.once, aligned, finalEq⟩

theorem execBlock_initializerEventChunks (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (scope : Nat)
    (statements : List Stmt) (value : Option Expr) (before ready : ExecutionState)
    (bound : bindAll environment.act before.nextScope pre
      { before with nextScope := before.nextScope + 1 } = .ok () ready) :
    ∃ outcome visits chunks,
      StatementReplay config { environment with scopes := (scope, before.nextScope) :: environment.scopes }
        fuel 0 statements ready outcome visits ∧
      FixedOrMaterializedInitializerForest config { environment with scopes := (scope, before.nextScope) :: environment.scopes } visits ∧
      visits.map StatementInvocation.statement = statements.take visits.length ∧
      (visits.map StatementInvocation.ordinal).Nodup ∧
      ChunksAlign (visits.map statementInvocation) chunks ∧
      (Goose.Proofs.Exit.stepState outcome).construction.events = ready.construction.events ++ chunks.flatten ∧
      execBlock (fuel + 1) config environment pre channels (.mk scope statements value) before =
        withScope environment scope before.nextScope (fun _ => blockContinuation fuel config
          { environment with scopes := (scope, before.nextScope) :: environment.scopes }
          channels value outcome) { before with nextScope := before.nextScope + 1 } := by
  obtain ⟨outcome, visits, replay, forest, execution⟩ :=
    execBlock_initializerForest fuel config environment pre channels scope statements value before ready bound
  obtain ⟨chunks, _, ordered, once, aligned, finalEq⟩ := statementReplay_initializerEventChunks replay
  exact ⟨outcome, visits, chunks, replay, forest, ordered, once, aligned, finalEq, execution⟩

#print axioms execBlock_initializerEventChunks
#print axioms statementReplay_invocationEvents
#print axioms statementReplay_initializerEventChunks
end Goose.Proofs.ConstructionGhostStatementEvents
