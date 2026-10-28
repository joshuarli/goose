import Goose.Proofs.ConstructionGhostStatements

namespace Goose.Proofs.ConstructionGhostResultScope
open Goose.Construct Goose.Proofs.ConstructionGhostStatements

def resultScopeContinuation (channels : List Channel) (value : Option Expr)
    (tailAction : Expr → EvalM (List Carrier)) (statements : ExecutionStep Flow) : ExecutionStep (Flow × List Carrier) :=
  match statements with
  | .ok flow state => (match flow, value with
      | .normal _, some expression => do pure (Flow.normal .unit, ← tailAction expression)
      | .normal _, none =>
          if channels.isEmpty then pure (flow, [])
          else match channels with
            | [.register .unit] => pure (flow, [.register .unit])
            | _ => fault .arity
      | flow, _ => pure (flow, [])) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

def resultScopeStart (environment : RuntimeActivation) (scope : Nat) (before : ExecutionState) : ExecutionState :=
  let scopeEnv := { environment with scopes := (scope, before.nextScope) :: environment.scopes }
  { before with nextScope := before.nextScope + 1, activations := before.activations.map (fun current =>
      if current.act == environment.act then { current with scopes := scopeEnv.scopes } else current) }

theorem execResultScope_boundReplay (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (scope : Nat)
    (statements : List Stmt) (value : Option Expr) (tailAction : RuntimeActivation → Expr → EvalM (List Carrier))
    (before ready : ExecutionState)
    (bound : bindAll environment.act before.nextScope pre (resultScopeStart environment scope before) = .ok () ready) :
    ∃ outcome visits,
      StatementReplay config { environment with scopes := (scope, before.nextScope) :: environment.scopes }
        fuel 0 statements ready outcome visits ∧
      execResultScope environment pre channels (.mk scope statements value)
        (fun environment statements => execStmts fuel config environment statements) tailAction before =
        withScope environment scope before.nextScope (fun _ => resultScopeContinuation channels value
          (tailAction { environment with scopes := (scope, before.nextScope) :: environment.scopes }) outcome)
          (resultScopeStart environment scope before) := by
  obtain ⟨visits, replay⟩ := statementReplay_exists fuel config
    { environment with scopes := (scope, before.nextScope) :: environment.scopes } 0 statements ready
  refine ⟨_, visits, replay, ?_⟩
  simp only [resultScopeStart] at bound
  simp only [execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope,
    resultScopeStart, bound, resultScopeContinuation]
  cases result : execStmts fuel config
    { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements ready <;> rfl

theorem execResultScope_statementReplay (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (scope : Nat) (statements : List Stmt)
    (tailAction : RuntimeActivation → Expr → EvalM (List Carrier)) (before : ExecutionState) :
    ∃ outcome visits,
      StatementReplay config { environment with scopes := (scope, before.nextScope) :: environment.scopes }
        fuel 0 statements (resultScopeStart environment scope before) outcome visits ∧
      execResultScope environment [] channels (.mk scope statements none)
        (fun environment statements => execStmts fuel config environment statements) tailAction before =
        withScope environment scope before.nextScope (fun _ => resultScopeContinuation channels none
          (tailAction { environment with scopes := (scope, before.nextScope) :: environment.scopes }) outcome)
          (resultScopeStart environment scope before) := by
  have bound : bindAll environment.act before.nextScope [] (resultScopeStart environment scope before) =
      .ok () (resultScopeStart environment scope before) := by simp [bindAll, bind, pure]
  exact execResultScope_boundReplay fuel config environment [] channels scope statements none tailAction before
    (resultScopeStart environment scope before) bound

#print axioms execResultScope_boundReplay

#print axioms execResultScope_statementReplay
end Goose.Proofs.ConstructionGhostResultScope
