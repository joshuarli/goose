import Goose.Lower.Validation.SourceReplacementWriterTypingVisibility
import Goose.Lower.Validation.SourceReplacementWriterTypingBlocks

namespace Goose.Lower.Validation.SourceReplacementWriterTyping

open Goose.Core Goose.Core.Sound SourceReplacementLexicalWriters

structure IndexedChildContext (env : TEnv) (parent : DemandNode) (index : Nat)
    (child : DemandNode) (after : TEnv) : Prop extends ChildContext env parent child after where
  visibleMatches : ∀ found, found ∈ after.visible ↔ found ∈ parent.visibleForChild env.visible index
  visibleOrigin : ∀ found, found ∈ after.visible → found ∈ env.visible ∨
    ∃ localVar, env.vars[found]? = some localVar ∧ localVar.scope ∈ ownScopeKeys parent ++ ownScopeKeys child

theorem IndexedChildContext.of_same {env after : TEnv} {parent child : DemandNode} {index : Nat}
    (context : ChildContext env parent child after) (visibleEq : after.visible = env.visible)
    (same : parent.visibleForChild env.visible index = env.visible) : IndexedChildContext env parent index child after := by
  refine ⟨context, ?_, ?_⟩
  · intro found
    rw [visibleEq, same]
  · intro found member
    exact Or.inl (visibleEq ▸ member)

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

theorem expression_indexed_child {env : TEnv} {expression : Expr} {type : Ty} {start finish index : Nat}
    (typed : tyExpr env expression start = .ok (type, finish)) {child : DemandNode}
    (row : (DemandNode.expression expression).child? index = some child) :
    ∃ after, IndexedChildContext env (.expression expression) index child after ∧ NodeTyped after child := by
  obtain ⟨after, context, source, visibleEq⟩ := expression_child typed (child_member row)
  exact ⟨after, .of_same context visibleEq rfl, source⟩

theorem slice_reference_indexed_child {env : TEnv} {expression : Expr} {type : Ty} {index : Nat}
    (typed : sliceRefTy env expression = some type) {child : DemandNode}
    (row : (DemandNode.expression expression).child? index = some child) :
    ∃ after, IndexedChildContext env (.expression expression) index child after ∧ NodeTyped after child := by
  obtain ⟨after, context, source, visibleEq⟩ := slice_reference_child typed (child_member row)
  exact ⟨after, .of_same context visibleEq rfl, source⟩

theorem place_indexed_child {env : TEnv} {place : Place} {info : PlaceInfo} {start finish index : Nat}
    (typed : tyPlace env place start = .ok (info, finish)) {child : DemandNode}
    (row : (DemandNode.place place).child? index = some child) :
    ∃ after, IndexedChildContext env (.place place) index child after ∧ NodeTyped after child := by
  obtain ⟨after, context, source, visibleEq⟩ := place_child typed (child_member row)
  exact ⟨after, .of_same context visibleEq rfl, source⟩

theorem view_indexed_child {env : TEnv} {view : View} {info : Ty × Bool} {start finish index : Nat}
    (typed : tyView env view start = .ok (info, finish)) {child : DemandNode}
    (row : (DemandNode.view view).child? index = some child) :
    ∃ after, IndexedChildContext env (.view view) index child after ∧ NodeTyped after child := by
  obtain ⟨after, context, source, visibleEq⟩ := view_child typed (child_member row)
  exact ⟨after, .of_same context visibleEq rfl, source⟩

theorem bound_indexed_child {env : TEnv} {bound : Bound} {start finish index : Nat}
    (typed : tyBound env bound start = .ok ((), finish)) {child : DemandNode}
    (row : (DemandNode.bound bound).child? index = some child) :
    ∃ after, IndexedChildContext env (.bound bound) index child after ∧ NodeTyped after child := by
  obtain ⟨after, context, source, visibleEq⟩ := bound_child typed (child_member row)
  exact ⟨after, .of_same context visibleEq rfl, source⟩

end Goose.Lower.Validation.SourceReplacementWriterTyping
