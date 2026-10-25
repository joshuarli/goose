import Goose.Lower.Validation.SourceReplacementWriterTypingIndexed

namespace Goose.Lower.Validation.SourceReplacementWriterTyping

open Goose.Core Goose.Core.Sound SourceReplacementLexicalWriters

private theorem block_child_cases {scope index : Nat} {statements : List Stmt} {value : Option Expr}
    {child : DemandNode} (row : (DemandNode.block (.mk scope statements value)).child? index = some child) :
    (∃ statement, child = .statement statement ∧ statements[index]? = some statement) ∨
      (∃ expression, child = .expression expression ∧ index = statements.length ∧ value = some expression) := by
  simp only [DemandNode.child?, DemandNode.children, List.getElem?_append] at row
  split at row
  · simp only [List.getElem?_map] at row
    cases selected : statements[index]? with
    | none => simp [selected] at row
    | some statement =>
      have same : .statement statement = child := by simpa [selected] using row
      exact Or.inl ⟨statement, same.symm, rfl⟩
  · rename_i outside
    simp only [List.length_map] at outside
    cases offset : index - statements.length with
    | zero =>
      cases valueAt : value with
      | none => simp [offset, valueAt] at row
      | some expression =>
        have same : .expression expression = child := by simpa [offset, valueAt] using row
        exact Or.inr ⟨expression, same.symm, by omega, rfl⟩
    | succ offset => simp [offset] at row

private theorem indexed_block_context {env after : TEnv} {scope index : Nat} {statements : List Stmt}
    {value : Option Expr} {child : DemandNode}
    (moduleEq : after.mod = env.mod) (varsEq : after.vars = env.vars) (implEq : after.impl = env.impl)
    (scopesEq : after.scopes = scope :: env.scopes)
    (visible : ∀ stack, StorageWalkVisible env (scope :: stack) → StorageWalkVisible after (scope :: stack))
    (visibilityMatches : ∀ found, found ∈ after.visible ↔
      found ∈ (DemandNode.block (.mk scope statements value)).visibleForChild env.visible index)
    (origin : ∀ found, found ∈ after.visible → found ∈ env.visible ∨
      ∃ localVar, env.vars[found]? = some localVar ∧ localVar.scope = scope) :
    IndexedChildContext env (.block (.mk scope statements value)) index child after := by
  refine ⟨⟨moduleEq, varsEq, implEq, scopesEq, ?_⟩, visibilityMatches, ?_⟩
  · intro stack previous
    change StorageWalkVisible env (scope :: stack) at previous
    apply (visible stack previous).mono
    intro found member
    rcases List.mem_cons.mp member with rfl | member
    · simp [ownScopeKeys]
    · simp [ownScopeKeys, member]
  · intro found member
    rcases origin found member with previous | ⟨localVar, row, declaredScope⟩
    · exact Or.inl previous
    · exact Or.inr ⟨localVar, row, by simp [ownScopeKeys, declaredScope]⟩

theorem block_indexed_child {env : TEnv} {block : Core.Block} {type : Ty} {start finish index : Nat}
    (typed : tyBlock env [] block start = .ok (type, finish)) {child : DemandNode}
    (row : (DemandNode.block block).child? index = some child) :
    ∃ after, IndexedChildContext env (.block block) index child after ∧ NodeTyped after child := by
  cases block with
  | mk scope statements value =>
    obtain ⟨fresh, declared, output, statementStart, valueStart, declaration, typedStatements, typedValue⟩ :=
      tyBlock_checked_children typed
    obtain ⟨rfl, rfl⟩ := (st_pure_ok _ _ _).mp declaration
    rcases block_child_cases row with ⟨statement, rfl, statementAt⟩ | ⟨expression, rfl, rfl, rfl⟩
    · obtain ⟨before, after, childStart, childFinish, source, moduleEq, varsEq, implEq, scopesEq,
        visibleEq, origin, visible⟩ := statements_index_context typedStatements statementAt
      have context : IndexedChildContext env (.block (.mk scope statements value)) index (.statement statement) before := by
        apply indexed_block_context (env := env) (scope := scope) moduleEq varsEq implEq scopesEq
        · intro stack previous
          exact visible (scope :: stack) previous (by simp)
        · intro found
          change found ∈ before.visible ↔ found ∈ (statements.take index).foldl _ env.visible
          have actual := visibleEq found
          rw [visible_statement_fold] at actual
          exact actual
        · exact origin
      refine ⟨before, context, .statement ?_ source⟩
      rw [scopesEq]
      exact List.mem_cons_self
    · have tables := tyStmts_tables statements typedStatements
      have context : IndexedChildContext env (.block (.mk scope statements (some expression))) statements.length
          (.expression expression) output := by
        apply indexed_block_context (env := env) (scope := scope) tables.1 tables.2.1 tables.2.2
          (tyStmts_scopes typedStatements)
        · intro stack previous
          have entered : StorageWalkVisible {env with scopes := scope :: env.scopes} (scope :: stack) := previous
          exact entered.tyStmts (by simp) typedStatements
        · intro found
          have actual := tyStmts_visible_members typedStatements found
          rw [visible_statement_fold] at actual
          simp only [DemandNode.visibleForChild, List.take_length]
          refine Eq.mp ?_ actual
          congr 3
        · exact fun found member => tyStmts_visible_origin typedStatements member
      exact ⟨output, context, .expression typedValue⟩

end Goose.Lower.Validation.SourceReplacementWriterTyping
