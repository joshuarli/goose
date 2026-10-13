import Goose.Core.Sound.Invert

/-!
Typing statements can add visible variables only when they declare them in
the current scope. This relation lets root proofs distinguish block-local
variables from names that were visible before the block.
-/

namespace Goose.Core.Sound
open Goose.Core

private theorem tyStmt_visibleScope (env : TEnv) (scope : Nat) (stmt : Stmt)
    (n n' : Nat) (env' : TEnv)
    (typed : tyStmt env scope stmt n = .ok (env', n')) :
    env'.mod = env.mod ∧ env'.vars = env.vars ∧ env'.scopes = env.scopes ∧
    ∀ x, x ∈ env'.visible → x ∈ env.visible ∨
      ∃ lv, env.vars[x]? = some lv ∧ lv.scope = scope := by
  cases stmt with
  | letS x value origin =>
    simp only [tyStmt] at typed
    inv at typed
    obtain ⟨_, lv, _, declared, _, _, _, _, _, _, rfl, _⟩ := typed
    have facts := declare_ok _ _ _ _ _ declared
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro y visible
    rcases List.mem_cons.1 visible with rfl | visible
    · exact Or.inr ⟨lv, facts.2.1, facts.2.2.1⟩
    · exact Or.inl visible
  | resize owner size fill origin =>
    cases fill
    all_goals simp only [tyStmt] at typed
    all_goals
      repeat first
        | (inv at typed)
        | (rcases typed with ⟨h, typed⟩)
        | (split at typed)
    all_goals
      repeat first
        | (inv at typed)
        | (rcases typed with ⟨h, typed⟩)
        | (split at typed)
    all_goals simp_all
  | ret value origin =>
    cases value
    all_goals simp only [tyStmt] at typed
    all_goals
      repeat first
        | (inv at typed)
        | (rcases typed with ⟨h, typed⟩)
        | (split at typed)
    all_goals
      repeat first
        | (inv at typed)
        | (rcases typed with ⟨h, typed⟩)
        | (split at typed)
    all_goals simp_all
  | ifS condition yes no origin =>
    cases no
    all_goals simp only [tyStmt] at typed
    all_goals
      repeat first
        | (inv at typed)
        | (rcases typed with ⟨h, typed⟩)
        | (split at typed)
    all_goals
      repeat first
        | (inv at typed)
        | (rcases typed with ⟨h, typed⟩)
        | (split at typed)
    all_goals simp_all
  | _ =>
    all_goals simp only [tyStmt] at typed
    all_goals
      repeat first
        | (inv at typed)
        | (rcases typed with ⟨h, typed⟩)
        | (split at typed)
    all_goals
      repeat first
        | (inv at typed)
        | (rcases typed with ⟨h, typed⟩)
        | (split at typed)
    all_goals simp_all

private theorem tyStmts_visibleScope (env : TEnv) (scope : Nat) (stmts : List Stmt)
    (n n' : Nat) (env' : TEnv)
    (typed : tyStmts env scope stmts n = .ok (env', n')) :
    env'.mod = env.mod ∧ env'.vars = env.vars ∧ env'.scopes = env.scopes ∧
    ∀ x, x ∈ env'.visible → x ∈ env.visible ∨
      ∃ lv, env.vars[x]? = some lv ∧ lv.scope = scope := by
  induction stmts generalizing env n with
  | nil =>
    simp only [tyStmts] at typed
    obtain ⟨rfl, rfl⟩ := (st_pure_ok _ _ _).1 typed
    exact ⟨rfl, rfl, rfl, fun _ visible => Or.inl visible⟩
  | cons stmt rest ih =>
    simp only [tyStmts] at typed
    obtain ⟨middle, next, head, tail⟩ := (st_bind_ok _ _ _ _).1 typed
    obtain ⟨modHead, varsHead, scopesHead, visibleHead⟩ := tyStmt_visibleScope _ _ _ _ _ _ head
    obtain ⟨modTail, varsTail, scopesTail, visibleTail⟩ := ih middle next tail
    refine ⟨modTail.trans modHead, varsTail.trans varsHead, scopesTail.trans scopesHead, ?_⟩
    intro x visible
    rcases visibleTail x visible with previous | ⟨lv, hvar, hscope⟩
    · exact visibleHead x previous
    · exact Or.inr ⟨lv, by simpa [varsHead] using hvar, hscope⟩

theorem tyBlock_innerVisible {env : TEnv} {block : Block} {n n' : Nat} {ty : Ty}
    (typed : tyBlock env [] block n = .ok (ty, n')) :
    ∃ inner next, block.scope ∉ env.scopes ∧
      tyStmts {env with scopes := block.scope :: env.scopes}
        block.scope block.stmts n = .ok (inner, next) ∧
      (match block.value with
       | none => ty = .unit ∧ n' = next
       | some e => tyExpr inner e next = .ok (ty, n')) ∧
      inner.mod = env.mod ∧ inner.vars = env.vars ∧
      inner.scopes = block.scope :: env.scopes ∧
      ∀ x, x ∈ inner.visible → x ∈ env.visible ∨
        ∃ lv, env.vars[x]? = some lv ∧ lv.scope = block.scope := by
  cases block with
  | mk scope stmts value =>
    cases value with
    | none =>
      obtain ⟨fresh, env1, start, inner, next, hdeclare, hstmts, hvalue⟩ :=
        tyBlock_ok env [] scope stmts none n ty n' typed
      simp only [declarePre, st_pure_ok, Prod.mk.injEq] at hdeclare
      obtain ⟨rfl, rfl⟩ := hdeclare
      have hvisible := tyStmts_visibleScope ({env with scopes := scope :: env.scopes})
        scope stmts _ next inner hstmts
      refine ⟨inner, next, fresh, hstmts, ?_, ?_, ?_, ?_, ?_⟩
      · exact hvalue
      · simpa using hvisible.1
      · simpa using hvisible.2.1
      · change inner.scopes = scope :: env.scopes
        exact hvisible.2.2.1
      · intro x visible
        rcases hvisible.2.2.2 x visible with source | ⟨lv, hvar, hscope⟩
        · exact Or.inl (by simpa using source)
        · exact Or.inr ⟨lv, hvar, hscope⟩
    | some e =>
      obtain ⟨fresh, env1, start, inner, next, hdeclare, hstmts, hvalue⟩ :=
        tyBlock_ok env [] scope stmts (some e) n ty n' typed
      simp only [declarePre, st_pure_ok, Prod.mk.injEq] at hdeclare
      obtain ⟨rfl, rfl⟩ := hdeclare
      have hvisible := tyStmts_visibleScope ({env with scopes := scope :: env.scopes})
        scope stmts _ next inner hstmts
      refine ⟨inner, next, fresh, hstmts, ?_, ?_, ?_, ?_, ?_⟩
      · exact hvalue
      · simpa using hvisible.1
      · simpa using hvisible.2.1
      · change inner.scopes = scope :: env.scopes
        exact hvisible.2.2.1
      · intro x visible
        rcases hvisible.2.2.2 x visible with source | ⟨lv, hvar, hscope⟩
        · exact Or.inl (by simpa using source)
        · exact Or.inr ⟨lv, hvar, hscope⟩

end Goose.Core.Sound
