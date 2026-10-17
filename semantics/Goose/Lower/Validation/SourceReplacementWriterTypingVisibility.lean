import Goose.Lower.Validation.SourceReplacementWriterTyping

namespace Goose.Lower.Validation.SourceReplacementWriterTyping

open Goose.Core Goose.Core.Sound

def StatementVisible (statement : Stmt) (visible : List VarId) : List VarId :=
  match statement with
  | .letS index _ _ => index :: visible
  | _ => visible

theorem tyStmt_visible {env after : TEnv} {scope start finish : Nat} (statement : Stmt)
    (typed : tyStmt env scope statement start = .ok (after, finish)) :
    after.visible = StatementVisible statement env.visible := by
  cases statement
  case' resize owner size fill origin => cases fill
  case' ifS condition thenBlock otherwise origin => cases otherwise
  case' ret value origin => cases value
  all_goals simp only [tyStmt] at typed
  all_goals
    repeat' first
    | (subst after; rfl)
    | contradiction
    | (simp only [chk, false_and, and_false, exists_false, exists_const, or_false, false_or,
        true_and, Prod.mk.injEq, Prod.exists, and_assoc, exists_eq_left, exists_and_left] at typed)
    | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
    | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
    | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
    | (split at typed)

theorem tyStmt_visible_origin {env after : TEnv} {scope start finish : Nat} {statement : Stmt}
    (typed : tyStmt env scope statement start = .ok (after, finish)) {index : VarId}
    (member : index ∈ after.visible) :
    index ∈ env.visible ∨ ∃ localVar, env.vars[index]? = some localVar ∧ localVar.scope = scope := by
  have output := tyStmt_visible statement typed
  cases statement with
  | letS binder expression origin =>
    obtain ⟨localVar, type, next, declared, source, passing, same⟩ := tyStmt_let_children typed
    rw [output] at member
    rcases List.mem_cons.mp member with rfl | previous
    · have facts := declare_ok _ _ _ _ _ declared
      exact Or.inr ⟨localVar, facts.2.1, facts.2.2.1⟩
    · exact Or.inl previous
  | _ => exact Or.inl (by simpa only [output, StatementVisible] using member)

theorem tyStmts_visible_origin {env after : TEnv} {scope start finish : Nat} {statements : List Stmt}
    (typed : tyStmts env scope statements start = .ok (after, finish)) {index : VarId}
    (member : index ∈ after.visible) :
    index ∈ env.visible ∨ ∃ localVar, env.vars[index]? = some localVar ∧ localVar.scope = scope := by
  induction statements generalizing env start with
  | nil =>
    obtain ⟨rfl, rfl⟩ := (st_pure_ok _ _ _).mp typed
    exact Or.inl member
  | cons statement statements ih =>
    obtain ⟨middle, next, head, tail⟩ := tyStmts_cons_children typed
    rcases ih tail with previous | ⟨localVar, row, declaredScope⟩
    · exact tyStmt_visible_origin head previous
    · exact Or.inr ⟨localVar, by simpa only [(tyStmt_tables statement head).2.1] using row, declaredScope⟩

theorem declarePre_visible_origin {env after : TEnv} {scope start finish : Nat} {pre : List (VarId × Ty)}
    (typed : declarePre env scope pre start = .ok (after, finish)) {index : VarId}
    (member : index ∈ after.visible) :
    index ∈ env.visible ∨ ∃ localVar, env.vars[index]? = some localVar ∧ localVar.scope = scope := by
  induction pre generalizing env start with
  | nil =>
    obtain ⟨rfl, rfl⟩ := (st_pure_ok _ _ _).mp typed
    exact Or.inl member
  | cons binding rest ih =>
    obtain ⟨binder, type⟩ := binding
    obtain ⟨localVar, next, declared, passing, tail⟩ := declarePre_cons_children typed
    rcases ih (env := {env with visible := binder :: env.visible}) tail with previous | found
    · rcases List.mem_cons.mp previous with rfl | previous
      · have facts := declare_ok _ _ _ _ _ declared
        exact Or.inr ⟨localVar, facts.2.1, facts.2.2.1⟩
      · exact Or.inl previous
    · exact Or.inr found

def DeclaredBy (statement : Stmt) (index : VarId) : Prop :=
  match statement with
  | .letS binder _ _ => index = binder
  | _ => False

theorem statementVisible_member (statement : Stmt) (visible : List VarId) (index : VarId) :
    index ∈ StatementVisible statement visible ↔ index ∈ visible ∨ DeclaredBy statement index := by
  cases statement <;> simp [StatementVisible, DeclaredBy, or_comm]

theorem demand_visibleAfter_member (statement : Stmt) (visible : List VarId) (index : VarId) :
    index ∈ (DemandNode.statement statement).visibleAfter visible ↔ index ∈ visible ∨ DeclaredBy statement index := by
  cases statement <;> simp only [DemandNode.visibleAfter, DeclaredBy, or_false]
  split
  · have present := List.contains_iff_mem.mp (by assumption : visible.contains _ = true)
    constructor
    · exact Or.inl
    · rintro (member | rfl)
      · exact member
      · exact present
  · simp [List.mem_cons, or_comm]

theorem visibleAfter_members_congr {before after : List VarId}
    (same : ∀ index, index ∈ before ↔ index ∈ after) (statement : Stmt) (index : VarId) :
    index ∈ (DemandNode.statement statement).visibleAfter before ↔
      index ∈ (DemandNode.statement statement).visibleAfter after := by
  simp only [demand_visibleAfter_member, same]

theorem visible_fold_members_congr (statements : List Stmt) {before after : List VarId}
    (same : ∀ index, index ∈ before ↔ index ∈ after) (index : VarId) :
    index ∈ statements.foldl (fun visible statement => (DemandNode.statement statement).visibleAfter visible) before ↔
      index ∈ statements.foldl (fun visible statement => (DemandNode.statement statement).visibleAfter visible) after := by
  induction statements generalizing before after with
  | nil => exact same index
  | cons statement statements ih =>
    simp only [List.foldl_cons]
    exact ih (visibleAfter_members_congr same statement)

theorem tyStmts_visible_members {env after : TEnv} {scope start finish : Nat} {statements : List Stmt}
    (typed : tyStmts env scope statements start = .ok (after, finish)) (index : VarId) :
    index ∈ after.visible ↔ index ∈ statements.foldl (fun visible statement =>
      (DemandNode.statement statement).visibleAfter visible) env.visible := by
  induction statements generalizing env start with
  | nil =>
    obtain ⟨rfl, rfl⟩ := (st_pure_ok _ _ _).mp typed
    rfl
  | cons statement statements ih =>
    obtain ⟨middle, next, head, tail⟩ := tyStmts_cons_children typed
    rw [ih tail]
    have first : ∀ index, index ∈ middle.visible ↔
        index ∈ (DemandNode.statement statement).visibleAfter env.visible := by
      intro index
      rw [tyStmt_visible statement head, statementVisible_member, demand_visibleAfter_member]
    change index ∈ statements.foldl _ middle.visible ↔ index ∈ statements.foldl _ ((DemandNode.statement statement).visibleAfter env.visible)
    exact visible_fold_members_congr statements first index

theorem statements_index_context {env output : TEnv} {statements : List Stmt}
    {statement : Stmt} {scope start finish index : Nat}
    (typed : tyStmts env scope statements start = .ok (output, finish))
    (row : statements[index]? = some statement) :
    ∃ before after childStart childFinish,
      tyStmt before scope statement childStart = .ok (after, childFinish) ∧
      before.mod = env.mod ∧ before.vars = env.vars ∧ before.impl = env.impl ∧ before.scopes = env.scopes ∧
      (∀ found, found ∈ before.visible ↔ found ∈ (statements.take index).foldl
        (fun visible statement => (DemandNode.statement statement).visibleAfter visible) env.visible) ∧
      (∀ found, found ∈ before.visible → found ∈ env.visible ∨
        ∃ localVar, env.vars[found]? = some localVar ∧ localVar.scope = scope) ∧
      (∀ stack, StorageWalkVisible env stack → scope ∈ stack → StorageWalkVisible before stack) := by
  induction statements generalizing env start index with
  | nil => simp at row
  | cons first rest ih =>
    obtain ⟨middle, next, head, tail⟩ := tyStmts_cons_children typed
    cases index with
    | zero =>
      have same : first = statement := Option.some.inj row
      subst statement
      exact ⟨env, middle, start, next, head, rfl, rfl, rfl, rfl, fun _ => Iff.rfl,
        fun _ member => Or.inl member, fun _ visible _ => visible⟩
    | succ index =>
      obtain ⟨before, after, childStart, childFinish, source, moduleEq, varsEq, implEq, scopesEq,
        visibleEq, origin, visible⟩ := ih tail (by simpa using row)
      have tables := tyStmt_tables first head
      refine ⟨before, after, childStart, childFinish, source, moduleEq.trans tables.1,
        varsEq.trans tables.2.1, implEq.trans tables.2.2, scopesEq.trans (tyStmt_scopes first head), ?_, ?_, ?_⟩
      · intro found
        rw [visibleEq]
        have firstVisible : ∀ found, found ∈ middle.visible ↔
            found ∈ (DemandNode.statement first).visibleAfter env.visible := by
          intro found
          rw [tyStmt_visible first head, statementVisible_member, demand_visibleAfter_member]
        exact visible_fold_members_congr (rest.take index) firstVisible found
      · intro found member
        rcases origin found member with previous | ⟨localVar, row, localScope⟩
        · exact tyStmt_visible_origin head previous
        · exact Or.inr ⟨localVar, by simpa only [tables.2.1] using row, localScope⟩
      · intro stack previous active
        exact visible stack (previous.tyStmt active head) active

theorem visible_statement_fold (statements : List Stmt) (visible : List VarId) :
    statements.foldl (fun active statement => (DemandNode.statement statement).visibleAfter active) visible =
      statements.foldl (fun active statement => match statement with
        | .letS binder _ _ => if active.contains binder then active else binder :: active
        | _ => active) visible := by
  have stepEq : (fun (active : List VarId) (statement : Stmt) =>
      (DemandNode.statement statement).visibleAfter active) =
      (fun active statement => match statement with
        | .letS binder _ _ => if active.contains binder then active else binder :: active
        | _ => active) := by
    funext active statement
    cases statement <;> rfl
  exact congrArg (fun step => statements.foldl step visible) stepEq

end Goose.Lower.Validation.SourceReplacementWriterTyping
