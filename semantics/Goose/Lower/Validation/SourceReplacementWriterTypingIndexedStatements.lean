import Goose.Lower.Validation.SourceReplacementWriterTypingIndexed

namespace Goose.Lower.Validation.SourceReplacementWriterTyping

open Goose.Core Goose.Core.Sound SourceReplacementLexicalWriters

private theorem child_member {parent child : DemandNode} {index : Nat}
    (source : parent.child? index = some child) : some child ∈ parent.children := by
  unfold DemandNode.child? at source
  cases row : parent.children[index]? with
  | none => simp [row] at source
  | some candidate =>
    cases candidate with
    | none => simp [row] at source
    | some actual =>
      have same : actual = child := by simpa [row] using source
      subst actual
      exact List.mem_of_getElem? row

private theorem same_statement_indexed_child {env : TEnv} {statement : Stmt} {child : DemandNode} {index : Nat}
    (same : (DemandNode.statement statement).visibleForChild env.visible index = env.visible)
    (typed : NodeTyped env child) :
    ∃ after, IndexedChildContext env (.statement statement) index child after ∧ NodeTyped after child :=
  ⟨env, .of_same (ChildContext.same env rfl) rfl same, typed⟩

private theorem forRange_expression_visible {env : TEnv} {binder : VarId} {lo hi expression : Expr}
    {body : Core.Block} {origin index : Nat}
    (row : (DemandNode.statement (.forRange binder lo hi body origin)).child? index = some (.expression expression)) :
    (DemandNode.statement (.forRange binder lo hi body origin)).visibleForChild env.visible index = env.visible := by
  cases index with
  | zero => rfl
  | succ index =>
    cases index with
    | zero => rfl
    | succ index => cases index <;> simp [DemandNode.child?, DemandNode.children] at row

private theorem forRange_block_index {binder : VarId} {lo hi : Expr} {body found : Core.Block} {origin index : Nat}
    (row : (DemandNode.statement (.forRange binder lo hi body origin)).child? index = some (.block found)) : index = 2 := by
  cases index with
  | zero => simp [DemandNode.child?, DemandNode.children] at row
  | succ index =>
    cases index with
    | zero => simp [DemandNode.child?, DemandNode.children] at row
    | succ index =>
      cases index with
      | zero => rfl
      | succ index => simp [DemandNode.child?, DemandNode.children] at row

private theorem forEach_view_visible {env : TEnv} {binder : VarId} {counter : Option VarId} {view found : View}
    {byRef : Bool} {body : Core.Block} {origin index : Nat}
    (row : (DemandNode.statement (.forEach binder counter view byRef body origin)).child? index = some (.view found)) :
    (DemandNode.statement (.forEach binder counter view byRef body origin)).visibleForChild env.visible index = env.visible := by
  cases index with
  | zero => rfl
  | succ index => cases index <;> simp [DemandNode.child?, DemandNode.children] at row

private theorem forEach_block_index {binder : VarId} {counter : Option VarId} {view : View}
    {byRef : Bool} {body found : Core.Block} {origin index : Nat}
    (row : (DemandNode.statement (.forEach binder counter view byRef body origin)).child? index = some (.block found)) : index = 1 := by
  cases index with
  | zero => simp [DemandNode.child?, DemandNode.children] at row
  | succ index =>
    cases index with
    | zero => rfl
    | succ index => simp [DemandNode.child?, DemandNode.children] at row

private theorem binder_fold_member (binders visible : List VarId) (found : VarId) :
    found ∈ binders.foldl (fun active binder => if active.contains binder then active else binder :: active) visible ↔
      found ∈ binders ++ visible := by
  induction binders generalizing visible with
  | nil => rfl
  | cons binder binders ih =>
    rw [List.foldl_cons, ih]
    have insert := demand_visibleAfter_member (.letS binder (.bool true) 0) visible found
    change found ∈ (if visible.contains binder then visible else binder :: visible) ↔
      found ∈ visible ∨ found = binder at insert
    simp only [List.mem_append, List.mem_cons]
    rw [insert]
    simp only [or_assoc, or_left_comm, or_comm]

private theorem range_visible_matches (env : TEnv) (binder : VarId) (lo hi : Expr)
    (body : Core.Block) (origin : Nat) (found : VarId) :
    found ∈ binder :: env.visible ↔
      found ∈ (DemandNode.statement (.forRange binder lo hi body origin)).visibleForChild env.visible 2 := by
  by_cases present : binder ∈ env.visible
  · have presentBool : env.visible.contains binder = true := List.contains_iff_mem.mpr present
    simp only [DemandNode.visibleForChild, beq_self_eq_true, presentBool,
      Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, List.mem_cons]
    constructor
    · rintro (rfl | member)
      · exact present
      · exact member
    · exact Or.inr
  · simp [DemandNode.visibleForChild, present]

private theorem loop_block_indexed_context (env : TEnv) (statement : Stmt) (body : Core.Block)
    (binders : List VarId) (index : Nat)
    (rows : ∀ found ∈ binders, ∃ localVar, env.vars[found]? = some localVar ∧ localVar.scope = body.scope)
    (visibilityMatches : ∀ found, found ∈ binders ++ env.visible ↔
      found ∈ (DemandNode.statement statement).visibleForChild env.visible index) :
    IndexedChildContext env (.statement statement) index (.block body)
      {env with loops := env.loops + 1, visible := binders ++ env.visible} := by
  refine ⟨loop_block_context env statement body binders ?_, visibilityMatches, ?_⟩
  · intro found member localVar row
    obtain ⟨actual, actualAt, actualScope⟩ := rows found member
    have same : actual = localVar := Option.some.inj (actualAt.symm.trans row)
    exact same ▸ actualScope
  · intro found member
    rcases List.mem_append.mp member with bound | previous
    · obtain ⟨localVar, row, declaredScope⟩ := rows found bound
      exact Or.inr ⟨localVar, row, by cases body; simpa [ownScopeKeys, Core.Block.scope] using declaredScope⟩
    · exact Or.inl previous

theorem statement_indexed_child {env output : TEnv} {statement : Stmt} {scope start finish childIndex : Nat}
    (typed : tyStmt env scope statement start = .ok (output, finish)) {child : DemandNode}
    (row : (DemandNode.statement statement).child? childIndex = some child) :
    ∃ after, IndexedChildContext env (.statement statement) childIndex child after ∧ NodeTyped after child := by
  have member := child_member row
  cases statement with
  | letS index expression origin =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨localVar, type, next, declared, source, rest⟩ := tyStmt_let_children typed
    exact same_statement_indexed_child (index := childIndex) rfl (.expression source)
  | rebind index expression origin =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨localVar, type, row, visible, reference, mutable, source, rest⟩ := tyStmt_rebind_children typed
    exact same_statement_indexed_child (index := childIndex) rfl (.expression source)
  | expr expression origin =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨type, source, rest⟩ := tyStmt_expr_children typed
    exact same_statement_indexed_child (index := childIndex) rfl (.expression source)
  | assertS expression origin =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    exact same_statement_indexed_child (index := childIndex) rfl (.expression (tyStmt_assert_children typed).1)
  | exit expression origin =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨integer, source, rest⟩ := tyStmt_exit_children typed
    exact same_statement_indexed_child (index := childIndex) rfl (.expression source)
  | assign place expression origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨info, next, placeTyped, expressionTyped, rest⟩ := tyStmt_assign_children typed
    rcases member with rfl | rfl
    · exact same_statement_indexed_child (index := childIndex) rfl (.place placeTyped)
    · exact same_statement_indexed_child (index := childIndex) rfl (.expression expressionTyped)
  | assignOp op place expression origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨info, integer, next, placeTyped, shape, expressionTyped, rest⟩ := tyStmt_assignOp_children typed
    rcases member with rfl | rfl
    · exact same_statement_indexed_child (index := childIndex) rfl (.place placeTyped)
    · exact same_statement_indexed_child (index := childIndex) rfl (.expression expressionTyped)
  | assignWhole place expression origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨info, element, next, placeTyped, shape, expressionTyped, rest⟩ := tyStmt_assignWhole_children typed
    rcases member with rfl | rfl
    · exact same_statement_indexed_child (index := childIndex) rfl (.place placeTyped)
    · exact same_statement_indexed_child (index := childIndex) rfl (.expression expressionTyped)
  | append place view origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨info, element, writable, next, placeTyped, shape, viewTyped, rest⟩ := tyStmt_append_children typed
    rcases member with rfl | rfl
    · exact same_statement_indexed_child (index := childIndex) rfl (.place placeTyped)
    · exact same_statement_indexed_child (index := childIndex) rfl (.view viewTyped)
  | popN place expression origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨info, element, integer, next, placeTyped, shape, expressionTyped, rest⟩ := tyStmt_popN_children typed
    rcases member with rfl | rfl
    · exact same_statement_indexed_child (index := childIndex) rfl (.place placeTyped)
    · exact same_statement_indexed_child (index := childIndex) rfl (.expression expressionTyped)
  | clear place origin =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨info, element, source, rest⟩ := tyStmt_clear_children typed
    exact same_statement_indexed_child (index := childIndex) rfl (.place source)
  | resize place expression fill origin =>
    obtain ⟨info, element, integer, next, valueFinish, placeTyped, shape, expressionTyped, fillTyped, rest⟩ :=
      tyStmt_resize_children typed
    cases fill with
    | none =>
      simp only [DemandNode.children, Option.map_none, List.mem_cons, List.not_mem_nil, or_false,
        Option.some.injEq, reduceCtorEq] at member
      rcases member with rfl | rfl
      · exact same_statement_indexed_child (index := childIndex) rfl (.place placeTyped)
      · exact same_statement_indexed_child (index := childIndex) rfl (.expression expressionTyped)
    | some fill =>
      simp only [DemandNode.children, Option.map_some, List.mem_cons, List.not_mem_nil, or_false,
        Option.some.injEq] at member
      rcases member with rfl | rfl | rfl
      · exact same_statement_indexed_child (index := childIndex) rfl (.place placeTyped)
      · exact same_statement_indexed_child (index := childIndex) rfl (.expression expressionTyped)
      · exact same_statement_indexed_child (index := childIndex) rfl (.expression fillTyped)
  | ifS condition yes no origin =>
    obtain ⟨conditionFinish, yesType, yesFinish, conditionTyped, yesTyped, noTyped, rest⟩ := tyStmt_if_children typed
    cases no with
    | none =>
      simp only [DemandNode.children, Option.map_none, List.mem_cons, List.not_mem_nil, or_false,
        Option.some.injEq, reduceCtorEq] at member
      rcases member with rfl | rfl
      · exact same_statement_indexed_child (index := childIndex) rfl (.expression conditionTyped)
      · exact same_statement_indexed_child (index := childIndex) rfl (.block yesTyped)
    | some no =>
      simp only [DemandNode.children, Option.map_some, List.mem_cons, List.not_mem_nil, or_false,
        Option.some.injEq] at member
      obtain ⟨noType, noSource⟩ := noTyped
      rcases member with rfl | rfl | rfl
      · exact same_statement_indexed_child (index := childIndex) rfl (.expression conditionTyped)
      · exact same_statement_indexed_child (index := childIndex) rfl (.block yesTyped)
      · exact same_statement_indexed_child (index := childIndex) rfl (.block noSource)
  | «while» condition body origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨conditionFinish, bodyType, conditionTyped, bodyTyped, rest⟩ := tyStmt_while_children typed
    rcases member with rfl | rfl
    · exact same_statement_indexed_child (index := childIndex) rfl (.expression conditionTyped)
    · exact ⟨_, loop_block_indexed_context env _ body [] childIndex (by simp) (fun _ => Iff.rfl), .block bodyTyped⟩
  | forRange index lo hi body origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨localVar, integer, lowerStart, lowerFinish, upperFinish, bodyType, declared,
      lowerTyped, upperTyped, shape, bodyTyped, rest⟩ := tyStmt_forRange_children typed
    rcases member with rfl | rfl | rfl
    · exact same_statement_indexed_child (index := childIndex) (forRange_expression_visible row) (.expression lowerTyped)
    · exact same_statement_indexed_child (index := childIndex) (forRange_expression_visible row) (.expression upperTyped)
    · have indexEq := forRange_block_index row
      refine ⟨_, loop_block_indexed_context env _ body [index] childIndex ?_ ?_, .block bodyTyped⟩
      · intro found member
        have same : found = index := List.mem_singleton.mp member
        subst found
        have facts := declare_ok _ _ _ _ _ declared
        exact ⟨localVar, facts.2.1, facts.2.2.1⟩
      · intro found
        rw [indexEq]
        exact range_visible_matches env _ _ _ _ _ found
  | forEach index counter view byRef body origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType, declared,
      counterDeclared, viewTyped, valid, bodyTyped, rest⟩ := tyStmt_forEach_children typed
    rcases member with rfl | rfl
    · exact same_statement_indexed_child (index := childIndex) (forEach_view_visible row) (.view viewTyped)
    · have indexEq := forEach_block_index row
      refine ⟨_, loop_block_indexed_context env _ body (index :: counter.toList) childIndex ?_ ?_, .block bodyTyped⟩
      · intro found member
        rcases List.mem_cons.mp member with rfl | counterMember
        · have facts := declare_ok _ _ _ _ _ declared
          exact ⟨localVar, facts.2.1, facts.2.2.1⟩
        · cases counter with
          | none => cases counterMember
          | some actual =>
            have same : found = actual := List.mem_singleton.mp counterMember
            subst found
            obtain ⟨number, localVar, row, declaredScope, type⟩ := (declareIndex_ok _ _ _ _ _ counterDeclared).2 actual rfl
            exact ⟨localVar, row, declaredScope⟩
      · intro found
        rw [indexEq]
        exact (binder_fold_member (index :: counter.toList) env.visible found).symm
  | ret expression origin =>
    cases expression with
    | none => simp [DemandNode.children] at member
    | some expression =>
      simp only [DemandNode.children, Option.map_some, List.mem_singleton, Option.some.injEq] at member
      subst child
      obtain ⟨expected, actual, impl, outside, implementation, result, source, rest⟩ := tyStmt_return_children typed
      exact same_statement_indexed_child (index := childIndex) rfl (.expression source)
  | print arguments origin =>
    obtain ⟨argument, argMember, childEq⟩ := List.mem_map.mp member
    cases argument with
    | text text => cases childEq
    | expr expression =>
      have same : child = .expression expression := Option.some.inj childEq.symm
      subst child
      obtain ⟨type, before, after, source, scalar⟩ := tyPrintArgs_expr_children (tyStmt_print_children typed).1 argMember
      exact same_statement_indexed_child (index := childIndex) rfl (.expression source)
  | brk origin => simp [DemandNode.children] at member
  | cont origin => simp [DemandNode.children] at member
  | abort message origin => simp [DemandNode.children] at member

end Goose.Lower.Validation.SourceReplacementWriterTyping
