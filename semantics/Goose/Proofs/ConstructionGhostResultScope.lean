import Goose.Proofs.ConstructionGhostResultScopeCore
import Goose.Proofs.ConstructionGhostBlockInitializers

namespace Goose.Proofs.ConstructionGhostResultScope
open Goose.Construct Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostBlockInitializers

theorem execResultScope_initializerForest (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (scope : Nat)
    (statements : List Stmt) (value : Option Expr) (tailAction : RuntimeActivation → Expr → EvalM (List Carrier))
    (before ready : ExecutionState)
    (bound : bindAll environment.act before.nextScope pre (resultScopeStart environment scope before) = .ok () ready) :
    ∃ outcome visits,
      StatementReplay config { environment with scopes := (scope, before.nextScope) :: environment.scopes }
        fuel 0 statements ready outcome visits ∧
      FixedOrMaterializedInitializerForest config
        { environment with scopes := (scope, before.nextScope) :: environment.scopes } visits ∧
      execResultScope environment pre channels (.mk scope statements value)
        (fun environment statements => execStmts fuel config environment statements) tailAction before =
        withScope environment scope before.nextScope (fun _ => resultScopeContinuation channels value
          (tailAction { environment with scopes := (scope, before.nextScope) :: environment.scopes }) outcome)
          (resultScopeStart environment scope before) := by
  obtain ⟨outcome, visits, replay, execution⟩ :=
    execResultScope_boundReplay fuel config environment pre channels scope statements value tailAction before ready bound
  exact ⟨outcome, visits, replay, statementReplay_initializerForest replay, execution⟩

#print axioms execResultScope_initializerForest
end Goose.Proofs.ConstructionGhostResultScope
