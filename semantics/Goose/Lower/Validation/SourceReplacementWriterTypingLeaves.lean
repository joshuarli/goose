import Goose.Lower.Validation.SourceReplacementWriterTypingExpressions

namespace Goose.Lower.Validation.SourceReplacementWriterTyping

open Goose.Core Goose.Core.Sound SourceReplacementLexicalWriters

private theorem same_child {env : TEnv} {parent child : DemandNode}
    (empty : ownScopeKeys parent = []) (typed : NodeTyped env child) :
    ∃ after, ChildContext env parent child after ∧ NodeTyped after child ∧ after.visible = env.visible :=
  ⟨env, ChildContext.same env empty, typed, rfl⟩

theorem slice_reference_child {env : TEnv} {expression : Expr} {type : Ty}
    (typed : sliceRefTy env expression = some type) {child : DemandNode}
    (member : some child ∈ (DemandNode.expression expression).children) :
    ∃ after, ChildContext env (.expression expression) child after ∧ NodeTyped after child ∧ after.visible = env.visible := by
  cases expression <;> simp only [sliceRefTy, reduceCtorEq] at typed
  case read place =>
    cases place <;> simp only [sliceRefTy, reduceCtorEq] at typed
    case var index =>
      have visible : index ∈ env.visible := storageWalk_sliceRef_visible typed
      cases row : env.vars[index]? with
      | none => simp [sliceRefTy, List.contains_iff_mem, visible, row] at typed
      | some localVar =>
        simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
        subst child
        apply same_child rfl
        apply NodeTyped.place (info := ⟨localVar.ty, localVar.kind == .mutable, true⟩) (start := 0) (finish := 0)
        simp [tyPlace, varOf, List.contains_iff_mem, visible, row, pure, bind, StateT.pure, StateT.bind,
          Except.pure, Except.bind]

theorem place_child {env : TEnv} {place : Place} {info : PlaceInfo} {start finish : Nat}
    (typed : tyPlace env place start = .ok (info, finish)) {child : DemandNode}
    (member : some child ∈ (DemandNode.place place).children) :
    ∃ after, ChildContext env (.place place) child after ∧ NodeTyped after child ∧ after.visible = env.visible := by
  cases place with
  | var index => simp [DemandNode.children] at member
  | global index => simp [DemandNode.children] at member
  | deref expression =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    cases shortcut : sliceRefTy env expression with
    | none =>
      obtain ⟨mutability, childFinish, source⟩ := tyPlace_deref_child shortcut typed
      exact same_child rfl (.expression source)
    | some type => exact same_child rfl (.sliceReference shortcut)
  | elem view index origin =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
    obtain ⟨viewStart, viewFinish, indexFinish, writable, integer, viewTyped, indexTyped⟩ := tyPlace_elem_children typed
    rcases member with rfl | rfl
    · exact same_child rfl (.view viewTyped)
    · exact same_child rfl (.expression indexTyped)
  | field owner index =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨ownerInfo, ownerFinish, source, tail⟩ := (st_bind_ok _ _ _ _).mp typed
    exact same_child rfl (.place source)

theorem view_child {env : TEnv} {view : View} {info : Ty × Bool} {start finish : Nat}
    (typed : tyView env view start = .ok (info, finish)) {child : DemandNode}
    (member : some child ∈ (DemandNode.view view).children) :
    ∃ after, ChildContext env (.view view) child after ∧ NodeTyped after child ∧ after.visible = env.visible := by
  cases view with
  | of place =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨placeInfo, next, source, tail⟩ := (st_bind_ok _ _ _ _).mp typed
    exact same_child rfl (.place source)
  | val expression =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨type, next, source, tail⟩ := (st_bind_ok _ _ _ _).mp typed
    exact same_child rfl (.expression source)

theorem bound_child {env : TEnv} {bound : Bound} {start finish : Nat}
    (typed : tyBound env bound start = .ok ((), finish)) {child : DemandNode}
    (member : some child ∈ (DemandNode.bound bound).children) :
    ∃ after, ChildContext env (.bound bound) child after ∧ NodeTyped after child ∧ after.visible = env.visible := by
  cases bound with
  | omitted => simp [DemandNode.children] at member
  | expr expression | fromEnd expression =>
    simp only [DemandNode.children, List.mem_singleton, Option.some.injEq] at member
    subst child
    obtain ⟨integer, next, source⟩ := tyBound_child typed
    exact same_child rfl (.expression source)

end Goose.Lower.Validation.SourceReplacementWriterTyping
