import Goose.Lower.Validation.SourceReplacementWriterTypingStatements

namespace Goose.Lower.Validation.SourceReplacementWriterTyping

open Goose.Core Goose.Core.Sound SourceReplacementLexicalWriters

private theorem statements_member_context {env output : TEnv} {statements : List Stmt}
    {statement : Stmt} {scope start finish : Nat}
    (typed : tyStmts env scope statements start = .ok (output, finish)) (member : statement ∈ statements) :
    ∃ before after childStart childFinish,
      tyStmt before scope statement childStart = .ok (after, childFinish) ∧
      before.mod = env.mod ∧ before.vars = env.vars ∧ before.impl = env.impl ∧ before.scopes = env.scopes ∧
      ∀ stack, StorageWalkVisible env stack → scope ∈ stack → StorageWalkVisible before stack := by
  induction statements generalizing env start with
  | nil => cases member
  | cons first rest ih =>
    obtain ⟨middle, next, head, tail⟩ := tyStmts_cons_children typed
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨env, middle, start, next, head, rfl, rfl, rfl, rfl, fun _ visible _ => visible⟩
    · obtain ⟨before, after, childStart, childFinish, source, moduleEq, varsEq, implEq, scopesEq, visible⟩ :=
        ih tail member
      have tables := tyStmt_tables first head
      refine ⟨before, after, childStart, childFinish, source, moduleEq.trans tables.1,
        varsEq.trans tables.2.1, implEq.trans tables.2.2, scopesEq.trans (tyStmt_scopes first head), ?_⟩
      intro stack previous active
      exact visible stack (previous.tyStmt active head) active

private theorem block_context {env after : TEnv} {scope : Nat} {statements : List Stmt}
    {value : Option Expr} {child : DemandNode}
    (moduleEq : after.mod = env.mod) (varsEq : after.vars = env.vars) (implEq : after.impl = env.impl)
    (scopesEq : after.scopes = scope :: env.scopes)
    (visible : ∀ stack, StorageWalkVisible env (scope :: stack) → StorageWalkVisible after (scope :: stack)) :
    ChildContext env (.block (.mk scope statements value)) child after := by
  refine ⟨moduleEq, varsEq, implEq, scopesEq, ?_⟩
  intro stack previous
  change StorageWalkVisible env (scope :: stack) at previous
  apply (visible stack previous).mono
  intro index member
  rcases List.mem_cons.mp member with rfl | member
  · simp [ownScopeKeys]
  · simp [ownScopeKeys, member]

theorem block_child {env : TEnv} {block : Core.Block} {pre : List (VarId × Ty)}
    {type : Ty} {start finish : Nat}
    (typed : tyBlock env pre block start = .ok (type, finish)) {child : DemandNode}
    (member : some child ∈ (DemandNode.block block).children) :
    ∃ after, ChildContext env (.block block) child after ∧ NodeTyped after child := by
  cases block with
  | mk scope statements value =>
    obtain ⟨fresh, declared, output, statementStart, valueStart, declaration, typedStatements, typedValue⟩ :=
      tyBlock_checked_children typed
    have declaredTables := declarePre_tables pre declaration
    have declaredScopes := declarePre_scopes declaration
    change declared.scopes = scope :: env.scopes at declaredScopes
    have declaredVisible : ∀ stack, StorageWalkVisible env (scope :: stack) →
        StorageWalkVisible declared (scope :: stack) := by
      intro stack visible
      have entered : StorageWalkVisible {env with scopes := scope :: env.scopes} (scope :: stack) := visible
      exact entered.declarePre (by simp) declaration
    change some child ∈ statements.map (some ∘ DemandNode.statement) ++ [value.map DemandNode.expression] at member
    rcases List.mem_append.mp member with statementMember | valueMember
    · obtain ⟨statement, inStatements, childEq⟩ := List.mem_map.mp statementMember
      have same : child = .statement statement := Option.some.inj childEq.symm
      subst child
      obtain ⟨before, after, childStart, childFinish, source, moduleEq, varsEq, implEq, scopesEq, visible⟩ :=
        statements_member_context typedStatements inStatements
      have context : ChildContext env (.block (.mk scope statements value)) (.statement statement) before := by
        apply block_context (env := env) (scope := scope) (moduleEq.trans declaredTables.1) (varsEq.trans declaredTables.2.1)
          (implEq.trans declaredTables.2.2) (scopesEq.trans declaredScopes)
        intro stack previous
        exact visible (scope :: stack) (declaredVisible stack previous) (by simp)
      refine ⟨before, context, .statement ?_ source⟩
      rw [scopesEq, declaredScopes]
      exact List.mem_cons_self
    · cases value with
      | none => simp at valueMember
      | some expression =>
        have same : child = .expression expression := by simpa using valueMember
        subst child
        have outputTables := tyStmts_tables statements typedStatements
        have context : ChildContext env (.block (.mk scope statements (some expression))) (.expression expression) output := by
          apply block_context (env := env) (scope := scope) (outputTables.1.trans declaredTables.1) (outputTables.2.1.trans declaredTables.2.1)
            (outputTables.2.2.trans declaredTables.2.2) ((tyStmts_scopes typedStatements).trans declaredScopes)
          intro stack previous
          exact (declaredVisible stack previous).tyStmts (by simp) typedStatements
        exact ⟨output, context, .expression typedValue⟩

theorem NodeTyped.child {env : TEnv} {parent child : DemandNode}
    (typed : NodeTyped env parent) (member : some child ∈ parent.children) :
    ∃ after, ChildContext env parent child after ∧ NodeTyped after child := by
  cases typed with
  | expression source =>
    obtain ⟨after, context, typed, visibleEq⟩ := expression_child source member
    exact ⟨after, context, typed⟩
  | sliceReference source =>
    obtain ⟨after, context, typed, visibleEq⟩ := slice_reference_child source member
    exact ⟨after, context, typed⟩
  | place source =>
    obtain ⟨after, context, typed, visibleEq⟩ := place_child source member
    exact ⟨after, context, typed⟩
  | view source =>
    obtain ⟨after, context, typed, visibleEq⟩ := view_child source member
    exact ⟨after, context, typed⟩
  | bound source =>
    obtain ⟨after, context, typed, visibleEq⟩ := bound_child source member
    exact ⟨after, context, typed⟩
  | statement active source => exact statement_child source member
  | block source => exact block_child source member

#print axioms NodeTyped.child

end Goose.Lower.Validation.SourceReplacementWriterTyping
