import Goose.Lower.Validation.SourceReplacementWriterTyping
import Goose.Lower.Validation.DereferenceTyping
import Goose.Lower.Validation.ExpressionTypingContentsSourceOps

namespace Goose.Lower.Validation.SourceReplacementWriterTyping

open Goose.Core Goose.Core.Sound SourceReplacementLexicalWriters SummaryPreservation

private theorem same_expression_child {env : TEnv} {expression : Expr} {child : DemandNode}
    (typed : NodeTyped env child) :
    ∃ after, ChildContext env (.expression expression) child after ∧ NodeTyped after child ∧ after.visible = env.visible :=
  ⟨env, ChildContext.same env rfl, typed, rfl⟩

private theorem expression_list_member {env : TEnv} {expressions : List Expr} {element : Ty}
    {start finish : Nat} (typed : tyExprsAs env element expressions start = .ok ((), finish))
    {expression : Expr} (member : expression ∈ expressions) :
    ∃ type before after, tyExpr env expression before = .ok (type, after) := by
  induction expressions generalizing start with
  | nil => cases member
  | cons first rest ih =>
    simp only [tyExprsAs] at typed
    obtain ⟨type, next, head, tail⟩ := (st_bind_ok _ _ _ _).mp typed
    by_cases same : (type == element) = true
    · simp only [same, ite_true] at tail
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨type, start, next, head⟩
      · exact ih tail member
    · simp [same, chk] at tail

private theorem struct_list_member {env : TEnv} {expressions : List Expr} {types : List Ty}
    {start finish : Nat} (typed : tyStructExprs env types expressions start = .ok ((), finish))
    {expression : Expr} (member : expression ∈ expressions) :
    ∃ type before after, tyExpr env expression before = .ok (type, after) := by
  induction expressions generalizing types start with
  | nil => cases member
  | cons first rest ih =>
    cases types with
    | nil => simp [tyStructExprs, rej_ok] at typed
    | cons expected types =>
      simp only [tyStructExprs] at typed
      obtain ⟨type, next, head, tail⟩ := (st_bind_ok _ _ _ _).mp typed
      by_cases same : (type == expected) = true
      · simp only [same, ite_true] at tail
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨type, start, next, head⟩
        · exact ih tail member
      · simp [same, chk] at tail

private theorem argument_list_member {env : TEnv} {callee : Impl} {parameters : List Param}
    {arguments : List Arg} {start finish : Nat}
    (typed : tyArgs env callee parameters arguments start = .ok ((), finish))
    (arity : parameters.length = arguments.length) {argument : Arg} (member : argument ∈ arguments) :
    ∃ before after, ArgumentTyping env argument before after := by
  induction arguments generalizing parameters start with
  | nil => cases member
  | cons first rest ih =>
    cases parameters with
    | nil => simp at arity
    | cons parameter parameters =>
      obtain ⟨next, head, tail⟩ := tyArgs_cons_children typed
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨start, next, head⟩
      · exact ih tail (by simpa using arity) member

theorem expression_child {env : TEnv} {expression : Expr} {type : Ty} {start finish : Nat}
    (typed : tyExpr env expression start = .ok (type, finish)) {child : DemandNode}
    (member : some child ∈ (DemandNode.expression expression).children) :
    ∃ after, ChildContext env (.expression expression) child after ∧ NodeTyped after child ∧ after.visible = env.visible := by
  cases expression with
  | lit integer value => simp [DemandNode.children] at member
  | bool value => simp [DemandNode.children] at member
  | read place =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨info, next, source, shape⟩ := tyExpr_read_place typed
    exact same_expression_child (.place source)
  | ref mutability place =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨info, next, source, shape, rest⟩ := tyExpr_ref_place typed
    exact same_expression_child (.place source)
  | pop place origin =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨info, before, after, source, rest⟩ := tyExpr_pop_owner typed
    exact same_expression_child (.place source)
  | slice mutability view low high origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨element, writable, viewStart, viewFinish, lowFinish, highFinish, viewTyped, lowTyped, highTyped, shape⟩ :=
      tyExpr_slice_children typed
    rcases member with rfl | rfl | rfl
    · exact same_expression_child (.view viewTyped)
    · exact same_expression_child (.bound lowTyped)
    · exact same_expression_child (.bound highTyped)
  | len view =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨info, next, source, rest⟩ := (st_bind_ok _ _ _ _).mp typed
    exact same_expression_child (.view source)
  | un op expression origin =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨before, after, integer, source, rest⟩ := tyExpr_un_child typed
    exact same_expression_child (.expression source)
  | not expression =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨next, source, shape⟩ := tyExpr_not_child typed
    exact same_expression_child (.expression source)
  | conv kind target expression origin =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨sourceType, targetType, before, after, source, rest⟩ := tyExpr_conversion_child typed
    exact same_expression_child (.expression source)
  | fill target expression =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨shape, element, size, before, after, targetEq, source⟩ := tyExpr_fill_child typed
    exact same_expression_child (.expression source)
  | bin op left right origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨leftStart, leftFinish, rightStart, rightFinish, integer, leftTyped, rightTyped, shape⟩ := tyExpr_bin_children typed
    rcases member with rfl | rfl
    · exact same_expression_child (.expression leftTyped)
    · exact same_expression_child (.expression rightTyped)
  | cmp op left right =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨leftType, rightType, next, last, leftTyped, rightTyped, rest⟩ := tyExpr_comparison_children typed
    rcases member with rfl | rfl
    · exact same_expression_child (.expression leftTyped)
    · exact same_expression_child (.expression rightTyped)
  | and left right | or left right =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    simp only [tyExpr] at typed
    obtain ⟨leftType, leftFinish, leftTyped, tail⟩ := (st_bind_ok _ _ _ _).mp typed
    obtain ⟨checked, rightStart, boolean, tail⟩ := (st_bind_ok _ _ _ _).mp tail
    obtain ⟨rightType, rightFinish, rightTyped, tail⟩ := (st_bind_ok _ _ _ _).mp tail
    rcases member with rfl | rfl
    · exact same_expression_child (.expression leftTyped)
    · exact same_expression_child (.expression rightTyped)
  | call function arguments origin =>
    obtain ⟨calleeContext, callee, before, after, resultStart, contextAt, implAt, arity, argsTyped, result⟩ :=
      tyExpr_call_tables typed
    obtain ⟨argument, argumentMember, childEq⟩ := List.mem_map.mp member
    obtain ⟨before, after, argumentTyped⟩ := argument_list_member argsTyped arity argumentMember
    cases argument with
    | byVal expression =>
      have same : child = .expression expression := Option.some.inj childEq.symm
      subst child
      obtain ⟨type, source⟩ := argumentTyped
      exact same_expression_child (.expression source)
    | byRef mutability place =>
      have same : child = .place place := Option.some.inj childEq.symm
      subst child
      obtain ⟨info, source⟩ := argumentTyped
      exact same_expression_child (.place source)
  | push place expression origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨info, element, ownerStart, ownerFinish, valueStart, valueFinish, ownerTyped, shape, valueTyped, rest⟩ :=
      tyExpr_push_children typed
    rcases member with rfl | rfl
    · exact same_expression_child (.place ownerTyped)
    · exact same_expression_child (.expression valueTyped)
  | ifE condition yes no =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨conditionFinish, yesFinish, conditionTyped, yesTyped, noTyped⟩ := tyExpr_ifE_children typed
    rcases member with rfl | rfl | rfl
    · exact same_expression_child (.expression conditionTyped)
    · exact ⟨exprEnv env, ChildContext.expressionEnv env rfl, .block yesTyped, rfl⟩
    · exact ⟨exprEnv env, ChildContext.expressionEnv env rfl, .block noTyped, rfl⟩
  | blockE block =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    exact ⟨exprEnv env, ChildContext.expressionEnv env rfl, .block typed, rfl⟩
  | arrLit array expressions =>
    obtain ⟨same, element, before, after, shape, count, children⟩ := tyExpr_arrayLiteral_children typed
    obtain ⟨expression, expressionMember, childEq⟩ := List.mem_map.mp member
    have same : child = .expression expression := Option.some.inj childEq.symm
    subst child
    obtain ⟨type, before, after, source⟩ := expression_list_member children expressionMember
    exact same_expression_child (.expression source)
  | structLit record expressions =>
    obtain ⟨same, descriptor, definitionFinish, before, after, definition, children⟩ := tyExpr_structLiteral_children typed
    obtain ⟨expression, expressionMember, childEq⟩ := List.mem_map.mp member
    have same : child = .expression expression := Option.some.inj childEq.symm
    subst child
    obtain ⟨type, before, after, source⟩ := struct_list_member children expressionMember
    exact same_expression_child (.expression source)

end Goose.Lower.Validation.SourceReplacementWriterTyping
