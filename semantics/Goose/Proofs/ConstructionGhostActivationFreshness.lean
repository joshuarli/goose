import Goose.Proofs.ConstructionGhostDirectArrayForest

namespace Goose.Proofs.ConstructionGhostActivationFreshness
open Goose.Construct Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostDeclaration
open Goose.Proofs.ExitExecution

theorem statementReplay_visitFresh {config : EvalConfig} {environment : RuntimeActivation}
    {fuel offset : Nat} {statements : List Stmt} {before : ExecutionState}
    {outcome : ExecutionStep Flow} {visits : List StatementInvocation}
    (replay : StatementReplay config environment fuel offset statements before outcome visits)
    (fresh : FreshActivations before) (visit : StatementInvocation) (member : visit ∈ visits) :
    FreshActivations visit.before ∧ FreshActivations (Goose.Proofs.Exit.stepState visit.outcome) := by
  induction replay with
  | timeout | done => simp at member
  | @next fuel offset statement rest before middle value outcome visits head tail ih =>
    have after := (evaluation_preservesFresh fuel config).statement environment statement before fresh
    simp only [head, Goose.Proofs.Exit.stepState] at after
    simp only [List.mem_cons] at member
    rcases member with same | later
    · subst visit; exact ⟨fresh, after⟩
    · exact ih after later
  | @breaking fuel offset statement rest before after value head =>
    simp only [List.mem_singleton] at member
    subst visit
    exact ⟨fresh, by simpa only [head, Goose.Proofs.Exit.stepState] using
      (evaluation_preservesFresh fuel config).statement environment statement before fresh⟩
  | @continuing fuel offset statement rest before after head =>
    simp only [List.mem_singleton] at member
    subst visit
    exact ⟨fresh, by simpa only [head, Goose.Proofs.Exit.stepState] using
      (evaluation_preservesFresh fuel config).statement environment statement before fresh⟩
  | @stopped fuel offset statement rest before after reason head =>
    simp only [List.mem_singleton] at member
    subst visit
    exact ⟨fresh, by simpa only [head, Goose.Proofs.Exit.stepState] using
      (evaluation_preservesFresh fuel config).statement environment statement before fresh⟩
  | @escaped fuel offset statement rest before after address carriers head =>
    simp only [List.mem_singleton] at member
    subst visit
    exact ⟨fresh, by simpa only [head, Goose.Proofs.Exit.stepState] using
      (evaluation_preservesFresh fuel config).statement environment statement before fresh⟩
  | @jumped fuel offset statement rest before after target kind head =>
    simp only [List.mem_singleton] at member
    subst visit
    exact ⟨fresh, by simpa only [head, Goose.Proofs.Exit.stepState] using
      (evaluation_preservesFresh fuel config).statement environment statement before fresh⟩

theorem statementReplay_visitActiveBelowNext {config : EvalConfig} {environment : RuntimeActivation}
    {fuel offset : Nat} {statements : List Stmt} {before : ExecutionState}
    {outcome : ExecutionStep Flow} {visits : List StatementInvocation}
    (replay : StatementReplay config environment fuel offset statements before outcome visits)
    (fresh : FreshActivations before) (visit : StatementInvocation) (member : visit ∈ visits)
    (active : ∃ activation ∈ visit.before.activations, activation.act = visit.activation) :
    visit.activation < visit.before.nextAct ∧
      (visit.before.activations.map (·.act)).Nodup := by
  obtain ⟨beforeFresh, afterFresh⟩ := statementReplay_visitFresh replay fresh visit member
  obtain ⟨activation, present, same⟩ := active
  exact ⟨by simpa [same] using beforeFresh.2 activation present, beforeFresh.1⟩

#print axioms statementReplay_visitActiveBelowNext
theorem entryScope_fresh (implementation : Goose.Core.ImplId) (vars : Array LocalVar) (scope : Nat) :
    let activation : RuntimeActivation := ⟨implementation, 0, vars, [], []⟩
    let activated := { ExecutionState.initial with nextAct := 1, activations := [activation] }
    FreshActivations (Goose.Proofs.ConstructionGhostResultScope.resultScopeStart activation scope activated) := by
  simp [Goose.Proofs.ConstructionGhostResultScope.resultScopeStart, FreshActivations, ExecutionState.initial]

#print axioms entryScope_fresh
#print axioms statementReplay_visitFresh
end Goose.Proofs.ConstructionGhostActivationFreshness
