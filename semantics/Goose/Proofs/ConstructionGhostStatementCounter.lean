import Goose.Proofs.ConstructionGhostStatementPaths
import Goose.Proofs.ConstructionActivationCounterTheorem

namespace Goose.Proofs.ConstructionGhostStatementCounter
open Goose.Construct Goose.Proofs.ConstructionGhostStatements
open Goose.Proofs.ConstructionActivationCounter Goose.Proofs.ConstructionActivationCounterEvaluation
open Goose.Proofs.ConstructionGhostResultScope

theorem statementReplay_visitCounter {config : EvalConfig} {environment : RuntimeActivation}
    {fuel offset : Nat} {statements : List Stmt} {before : ExecutionState} {outcome : ExecutionStep Flow}
    {visits : List StatementInvocation} (replay : StatementReplay config environment fuel offset statements before outcome visits)
    (visit : StatementInvocation) (member : visit ∈ visits) : before.nextAct ≤ visit.before.nextAct := by
  induction replay with
  | timeout | done => simp at member
  | @next fuel offset statement rest before middle value outcome visits head tail ih =>
      have bound := (evaluation_preservesActivationCounter fuel config).statement environment statement before
      simp only [head, Goose.Proofs.Exit.stepState] at bound
      simp only [List.mem_cons] at member
      rcases member with same | later
      · subst visit; exact Nat.le_refl _
      · exact Nat.le_trans bound (ih later)
  | breaking head | continuing head | stopped head | escaped head | jumped head =>
      simp only [List.mem_singleton] at member
      subst visit
      exact Nat.le_refl _

theorem activationReplay_visitCounter {config : EvalConfig} {activation : RuntimeActivation}
    {pre : List (Goose.Core.VarId × Value)} {scope fuel offset : Nat} {statements : List Stmt}
    {before ready : ExecutionState} {outcome : ExecutionStep Flow} {visits : List StatementInvocation}
    (bound : bindAll activation.act before.nextScope pre (resultScopeStart activation scope before) = .ok () ready)
    (replay : StatementReplay config { activation with scopes := (scope, before.nextScope) :: activation.scopes }
      fuel offset statements ready outcome visits)
    (visit : StatementInvocation) (member : visit ∈ visits) : before.nextAct ≤ visit.before.nextAct := by
  have binding := counter_bindAll activation.act before.nextScope pre (resultScopeStart activation scope before)
  rw [bound] at binding
  simp only [Goose.Proofs.Exit.stepState, resultScopeStart] at binding
  exact Nat.le_trans binding (statementReplay_visitCounter replay visit member)

theorem activationReplay_visitAfterAllocation {config : EvalConfig} {activation : RuntimeActivation}
    {pre : List (Goose.Core.VarId × Value)} {scope fuel offset : Nat} {statements : List Stmt}
    {before ready : ExecutionState} {outcome : ExecutionStep Flow} {visits : List StatementInvocation}
    (allocated : activation.act < before.nextAct)
    (bound : bindAll activation.act before.nextScope pre (resultScopeStart activation scope before) = .ok () ready)
    (replay : StatementReplay config { activation with scopes := (scope, before.nextScope) :: activation.scopes }
      fuel offset statements ready outcome visits)
    (visit : StatementInvocation) (member : visit ∈ visits) : activation.act < visit.before.nextAct :=
  Nat.lt_of_lt_of_le allocated (activationReplay_visitCounter bound replay visit member)

#print axioms activationReplay_visitCounter
#print axioms activationReplay_visitAfterAllocation
#print axioms statementReplay_visitCounter
end Goose.Proofs.ConstructionGhostStatementCounter
