import Goose.Lower.Validation.SourceReplacementWriterTypingLeaves

namespace Goose.Lower.Validation.SourceReplacementWriterTyping

open Goose.Core Goose.Core.Sound SourceReplacementLexicalWriters

private theorem same_statement_child {env : TEnv} {statement : Stmt} {child : DemandNode}
    (typed : NodeTyped env child) :
    ∃ after, ChildContext env (.statement statement) child after ∧ NodeTyped after child :=
  ⟨env, ChildContext.same env rfl, typed⟩

theorem loop_block_context (env : TEnv) (statement : Stmt) (body : Core.Block)
    (binders : List VarId)
    (bindingsScoped : ∀ index ∈ binders, ∀ localVar, env.vars[index]? = some localVar → localVar.scope = body.scope) :
    ChildContext env (.statement statement) (.block body)
      { env with loops := env.loops + 1, visible := binders ++ env.visible } := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro stack visible
  change StorageWalkVisible env stack at visible
  simp only [ownScopeKeys, List.append_nil]
  change StorageWalkVisible { env with visible := binders ++ env.visible }
    (ownScopeKeys (.block body) ++ stack)
  have extended : StorageWalkVisible env (body.scope :: stack) :=
    visible.mono (fun scope member => List.mem_cons_of_mem _ member)
  have output := extended.prepend binders (by
    intro index member localVar row
    rw [bindingsScoped index member localVar row]
    exact List.mem_cons_self)
  cases body
  exact output

theorem statement_child {env output : TEnv} {statement : Stmt} {scope start finish : Nat}
    (typed : tyStmt env scope statement start = .ok (output, finish)) {child : DemandNode}
    (member : some child ∈ (DemandNode.statement statement).children) :
    ∃ after, ChildContext env (.statement statement) child after ∧ NodeTyped after child := by
  cases statement with
  | letS index expression origin =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨localVar, type, next, declared, source, rest⟩ := tyStmt_let_children typed
    exact same_statement_child (.expression source)
  | rebind index expression origin =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨localVar, type, row, visible, reference, mutable, source, rest⟩ := tyStmt_rebind_children typed
    exact same_statement_child (.expression source)
  | expr expression origin =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨type, source, rest⟩ := tyStmt_expr_children typed
    exact same_statement_child (.expression source)
  | assertS expression origin =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    exact same_statement_child (.expression (tyStmt_assert_children typed).1)
  | exit expression origin =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨integer, source, rest⟩ := tyStmt_exit_children typed
    exact same_statement_child (.expression source)
  | assign place expression origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨info, next, placeTyped, expressionTyped, rest⟩ := tyStmt_assign_children typed
    rcases member with rfl | rfl
    · exact same_statement_child (.place placeTyped)
    · exact same_statement_child (.expression expressionTyped)
  | assignOp op place expression origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨info, integer, next, placeTyped, shape, expressionTyped, rest⟩ := tyStmt_assignOp_children typed
    rcases member with rfl | rfl
    · exact same_statement_child (.place placeTyped)
    · exact same_statement_child (.expression expressionTyped)
  | assignWhole place expression origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨info, element, next, placeTyped, shape, expressionTyped, rest⟩ := tyStmt_assignWhole_children typed
    rcases member with rfl | rfl
    · exact same_statement_child (.place placeTyped)
    · exact same_statement_child (.expression expressionTyped)
  | append place view origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨info, element, writable, next, placeTyped, shape, viewTyped, rest⟩ := tyStmt_append_children typed
    rcases member with rfl | rfl
    · exact same_statement_child (.place placeTyped)
    · exact same_statement_child (.view viewTyped)
  | popN place expression origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨info, element, integer, next, placeTyped, shape, expressionTyped, rest⟩ := tyStmt_popN_children typed
    rcases member with rfl | rfl
    · exact same_statement_child (.place placeTyped)
    · exact same_statement_child (.expression expressionTyped)
  | clear place origin =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨info, element, source, rest⟩ := tyStmt_clear_children typed
    exact same_statement_child (.place source)
  | resize place expression fill origin =>
    obtain ⟨info, element, integer, next, valueFinish, placeTyped, shape, expressionTyped, fillTyped, rest⟩ :=
      tyStmt_resize_children typed
    cases fill with
    | none =>
      simp only [DemandNode.children, Option.map_none, List.mem_cons, List.not_mem_nil, or_false,
        Option.some.injEq, reduceCtorEq] at member
      rcases member with rfl | rfl
      · exact same_statement_child (.place placeTyped)
      · exact same_statement_child (.expression expressionTyped)
    | some fill =>
      simp only [DemandNode.children, Option.map_some, List.mem_cons, List.not_mem_nil, or_false,
        Option.some.injEq] at member
      rcases member with rfl | rfl | rfl
      · exact same_statement_child (.place placeTyped)
      · exact same_statement_child (.expression expressionTyped)
      · exact same_statement_child (.expression fillTyped)
  | ifS condition yes no origin =>
    obtain ⟨conditionFinish, yesType, yesFinish, conditionTyped, yesTyped, noTyped, rest⟩ := tyStmt_if_children typed
    cases no with
    | none =>
      simp only [DemandNode.children, Option.map_none, List.mem_cons, List.not_mem_nil, or_false,
        Option.some.injEq, reduceCtorEq] at member
      rcases member with rfl | rfl
      · exact same_statement_child (.expression conditionTyped)
      · exact same_statement_child (.block yesTyped)
    | some no =>
      simp only [DemandNode.children, Option.map_some, List.mem_cons, List.not_mem_nil, or_false,
        Option.some.injEq] at member
      obtain ⟨noType, noSource⟩ := noTyped
      rcases member with rfl | rfl | rfl
      · exact same_statement_child (.expression conditionTyped)
      · exact same_statement_child (.block yesTyped)
      · exact same_statement_child (.block noSource)
  | «while» condition body origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨conditionFinish, bodyType, conditionTyped, bodyTyped, rest⟩ := tyStmt_while_children typed
    rcases member with rfl | rfl
    · exact same_statement_child (.expression conditionTyped)
    · exact ⟨_, loop_block_context env _ body [] (by simp), .block bodyTyped⟩
  | forRange index lo hi body origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨localVar, integer, lowerStart, lowerFinish, upperFinish, bodyType, declared,
      lowerTyped, upperTyped, shape, bodyTyped, rest⟩ := tyStmt_forRange_children typed
    rcases member with rfl | rfl | rfl
    · exact same_statement_child (.expression lowerTyped)
    · exact same_statement_child (.expression upperTyped)
    · refine ⟨_, loop_block_context env _ body [index] ?_, .block bodyTyped⟩
      intro actual member candidate row
      have same : actual = index := List.mem_singleton.mp member
      subst actual
      have facts := declare_ok _ _ _ _ _ declared
      have same : localVar = candidate := Option.some.inj (facts.2.1.symm.trans row)
      subst candidate
      exact facts.2.2.1
  | forEach index counter view byRef body origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType, declared,
      counterDeclared, viewTyped, valid, bodyTyped, rest⟩ := tyStmt_forEach_children typed
    rcases member with rfl | rfl
    · exact same_statement_child (.view viewTyped)
    · refine ⟨_, loop_block_context env _ body (index :: counter.toList) ?_, .block bodyTyped⟩
      intro actual member candidate row
      rcases List.mem_cons.mp member with rfl | member
      · have facts := declare_ok _ _ _ _ _ declared
        have same : localVar = candidate := Option.some.inj (facts.2.1.symm.trans row)
        subst candidate
        exact facts.2.2.1
      · exact storageWalk_declared_index_scope counterDeclared actual member candidate row
  | ret expression origin =>
    cases expression with
    | none => simp [DemandNode.children] at member
    | some expression =>
      simp only [DemandNode.children, Option.map_some, List.mem_singleton, Option.some.injEq] at member
      subst child
      obtain ⟨expected, actual, impl, outside, implementation, result, source, rest⟩ := tyStmt_return_children typed
      exact same_statement_child (.expression source)
  | print arguments origin =>
    obtain ⟨argument, argMember, childEq⟩ := List.mem_map.mp member
    cases argument with
    | text text => cases childEq
    | expr expression =>
      have same : child = .expression expression := Option.some.inj childEq.symm
      subst child
      obtain ⟨type, before, after, source, scalar⟩ := tyPrintArgs_expr_children (tyStmt_print_children typed).1 argMember
      exact same_statement_child (.expression source)
  | brk origin => simp [DemandNode.children] at member
  | cont origin => simp [DemandNode.children] at member
  | abort message origin => simp [DemandNode.children] at member

end Goose.Lower.Validation.SourceReplacementWriterTyping
