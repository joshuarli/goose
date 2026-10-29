import Goose.Proofs.ConstructionGhostModuleResultEvents
import Goose.Proofs.ConstructionGhostEventOwnership

namespace Goose.Proofs.ConstructionGhostModuleEntryEventOwnership
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionGhostModuleResultEvents Goose.Proofs.ConstructionGhostEventOwnership
open Goose.Proofs.ConstructionGhostSourceGlobal Goose.Proofs.ConstructionGhostResultScope Goose.Proofs.ConstructionGhostStatements
open Goose.Proofs.ConstructionGhostStatementEvents Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostInvocationEventChunks

theorem moduleEntry_tail_eventOwnership (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (implementation : Impl) (scope : Nat) (statements : List Stmt) (tail : Option Expr) (activated before : ExecutionState)
    (channels : List Channel) (callResult : ExecutionStep (List Carrier)) (outcome : ExecutionStep Flow)
    (visits : List StatementInvocation)
    (found : config.module.impls[activation.implementation]? = some implementation)
    (body : implementation.body = .mk scope statements tail)
    (replay : StatementReplay config { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
      fuel 0 statements (resultScopeStart activation scope activated) outcome visits)
    (supported : ∀ sourceFuel localVar expression origin, .letS localVar expression origin ∈ statements →
      FuelSupport config sourceFuel
        (.value { activation with scopes := (scope, activated.nextScope) :: activation.scopes } expression))
    (call : callResult = ((enterActivation (fuel + 2) config activation [] implementation.body 0 >>= fun carriers =>
      deliverCarriers (fuel + 2) config.layout channels carriers 0) activated))
    (moduleResult : runModule (fuel + 3) config before = entryCallResult callResult) :
    ∃ chunks continuation,
      ChunksAlign (visits.map statementInvocation) chunks ∧
      OwnsEvents (visits.map statementInvocation) chunks ∧
      visits.map StatementInvocation.statement = statements.take visits.length ∧
      (visits.map StatementInvocation.ordinal).Nodup ∧
      (Goose.Proofs.Exit.stepState (runModule (fuel + 3) config before)).construction.events =
        (resultScopeStart activation scope activated).construction.events ++ chunks.flatten ++ continuation ∧
      (∀ other, ChunksAlign (visits.map statementInvocation) other → chunks = other) ∧
      (∀ other, (Goose.Proofs.Exit.stepState (runModule (fuel + 3) config before)).construction.events =
        (resultScopeStart activation scope activated).construction.events ++ chunks.flatten ++ other → continuation = other) := by
  obtain ⟨chunks, aligned, events, order, once, ownership, unique⟩ := statementReplay_eventOwnership replay
  obtain ⟨continuation, kept⟩ := moduleEntry_tail_replayPrefix fuel config activation implementation scope statements tail activated before channels
    callResult outcome visits found body replay supported call moduleResult
  have finalEq : (Goose.Proofs.Exit.stepState (runModule (fuel + 3) config before)).construction.events =
      (resultScopeStart activation scope activated).construction.events ++ chunks.flatten ++ continuation := by
    rw [kept, events, List.append_assoc]
  refine ⟨chunks, continuation, aligned, ownership, order, once, finalEq, unique, ?_⟩
  intro other otherEq
  exact (List.append_right_inj _).mp (finalEq.symm.trans otherEq)

#print axioms moduleEntry_tail_eventOwnership
end Goose.Proofs.ConstructionGhostModuleEntryEventOwnership
