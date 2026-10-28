import Goose.Proofs.ConstructionGhostCallHistoryInversion
import Goose.Proofs.ConstructionGhostStatements

namespace Goose.Proofs.ConstructionGhostStatementPaths
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostCallHistoryInversion
open Goose.Proofs.ConstructionGhostStatements

inductive StatementPath : Nat → List Nat → Nat → Prop
  | here (offset : Nat) : StatementPath offset [0] offset
  | next (offset ordinal : Nat) (suffix : List Nat) (tail : StatementPath (offset + 1) suffix ordinal) :
      StatementPath offset (1 :: suffix) ordinal

theorem StatementPath.ordinal_bound {offset ordinal : Nat} {suffix : List Nat}
    (path : StatementPath offset suffix ordinal) : offset ≤ ordinal := by
  induction path <;> omega

theorem StatementPath.uniqueOrdinal {offset first second : Nat} {suffix : List Nat}
    (left : StatementPath offset suffix first) (right : StatementPath offset suffix second) : first = second := by
  induction left generalizing second with
  | here offset => cases right; rfl
  | next offset ordinal suffix tail ih => cases right with | next _ _ _ other => exact ih other

theorem StatementPath.uniquePath {offset ordinal : Nat} {first second : List Nat}
    (left : StatementPath offset first ordinal) (right : StatementPath offset second ordinal) : first = second := by
  induction left generalizing second with
  | here offset => cases right with
    | here => rfl
    | next _ _ _ tail =>
        have lower := tail.ordinal_bound
        omega
  | next offset ordinal suffix tail ih =>
      cases right with
      | here =>
          have lower := tail.ordinal_bound
          omega
      | next _ _ _ other => exact congrArg (List.cons 1) (ih other)

#print axioms StatementPath.uniqueOrdinal
#print axioms StatementPath.uniquePath

theorem statementReplay_sourcePaths {config : EvalConfig} {environment : RuntimeActivation}
    {fuel offset : Nat} {statements : List Stmt} {before : ExecutionState} {outcome : ExecutionStep Flow}
    {visits : List StatementInvocation} (replay : StatementReplay config environment fuel offset statements before outcome visits) :
    ∀ path, SourceHistory config fuel path (.statements environment statements) before outcome →
      ∀ visit ∈ visits, ∃ suffix, StatementPath offset suffix visit.ordinal ∧
        SourceHistory config visit.fuel (path ++ suffix) (.statement environment visit.statement) visit.before visit.outcome := by
  induction replay with
  | timeout | done => intros; simp_all
  | @next fuel offset statement rest before middle value outcome visits head tail ih =>
      intro path history visit member
      simp only [List.mem_cons] at member
      rcases member with same | later
      · subst visit
        refine ⟨[0], .here offset, ?_⟩
        have child := statements_head_history history fuel environment statement rest rfl rfl
        rw [head] at child
        exact child
      · have tailHistory := statements_tail_history history fuel environment statement rest value middle rfl rfl head
        rw [tail.sound] at tailHistory
        obtain ⟨suffix, suffixPath, child⟩ := ih (path ++ [1]) tailHistory visit later
        refine ⟨1 :: suffix, .next offset visit.ordinal suffix suffixPath, ?_⟩
        simpa [List.append_assoc] using child
  | @breaking fuel offset statement rest before after value head =>
      intro path history visit member
      simp only [List.mem_singleton] at member
      subst visit
      refine ⟨[0], .here offset, ?_⟩
      have child := statements_head_history history fuel environment statement rest rfl rfl
      rw [head] at child
      exact child
  | @continuing fuel offset statement rest before after head =>
      intro path history visit member
      simp only [List.mem_singleton] at member
      subst visit
      refine ⟨[0], .here offset, ?_⟩
      have child := statements_head_history history fuel environment statement rest rfl rfl
      rw [head] at child
      exact child
  | @stopped fuel offset statement rest before after reason head =>
      intro path history visit member
      simp only [List.mem_singleton] at member
      subst visit
      refine ⟨[0], .here offset, ?_⟩
      have child := statements_head_history history fuel environment statement rest rfl rfl
      rw [head] at child
      exact child
  | @escaped fuel offset statement rest before after address carriers head =>
      intro path history visit member
      simp only [List.mem_singleton] at member
      subst visit
      refine ⟨[0], .here offset, ?_⟩
      have child := statements_head_history history fuel environment statement rest rfl rfl
      rw [head] at child
      exact child
  | @jumped fuel offset statement rest before after target kind head =>
      intro path history visit member
      simp only [List.mem_singleton] at member
      subst visit
      refine ⟨[0], .here offset, ?_⟩
      have child := statements_head_history history fuel environment statement rest rfl rfl
      rw [head] at child
      exact child

#print axioms statementReplay_sourcePaths
end Goose.Proofs.ConstructionGhostStatementPaths
