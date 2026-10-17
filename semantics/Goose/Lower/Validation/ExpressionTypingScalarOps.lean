import Goose.Lower.Validation.ExpressionTypingAggregateOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem tyExpr_conversion_child {env : Core.TEnv} {kind : ConvKind} {target ty : Ty}
    {expr : Expr} {origin : OriginId} {start finish : Nat}
    (source : Core.tyExpr env (.conv kind target expr origin) start = .ok (ty, finish)) :
    ∃ src dst childStart childFinish,
      Core.tyExpr env expr childStart = .ok (.int src, childFinish) ∧ target = .int dst ∧ ty = .int dst ∧
      (kind = .widen → dst.minVal ≤ src.minVal ∧ src.maxVal ≤ dst.maxVal) := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, childStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨childTy, childFinish, childTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨src, next, integer, source⟩ := (st_bind_ok _ _ _ _).mp source
  have shape := (requireInt_ok _ _ _ _).mp integer
  rw [shape.1] at childTyped
  cases target with
  | int dst =>
    cases kind with
    | widen =>
      by_cases range : dst.minVal ≤ src.minVal ∧ src.maxVal ≤ dst.maxVal
      · simp only [range] at source
        have result := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
        exact ⟨src, dst, childStart, childFinish, childTyped, rfl, result, fun _ => range⟩
      · simp only [range, ite_false] at source
        change ((rej .type "a widening that does not preserve every value" : Core.T Unit) >>=
          fun _ => pure (.int dst)) next = .ok (ty, finish) at source
        obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
        exact (rej_ok _ _ _ _).mp rejected |>.elim
    | as | asUnchecked =>
      have result := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      exact ⟨src, dst, childStart, childFinish, childTyped, rfl, result, by intro h; cases h⟩
  | _ => exact (rej_ok _ _ _ _).mp source |>.elim

theorem tyExpr_comparison_children {env : Core.TEnv} {op : CmpOp} {left right : Expr}
    {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.cmp op left right) start = .ok (ty, finish)) :
    ∃ leftTy rightTy leftFinish rightFinish,
      Core.tyExpr env left start = .ok (leftTy, leftFinish) ∧
      Core.tyExpr env right leftFinish = .ok (rightTy, rightFinish) ∧ ty = .bool ∧
      ((∃ intTy, leftTy = .int intTy ∧ rightTy = .int intTy) ∨
        (leftTy = .bool ∧ rightTy = .bool ∧ (op = .eq ∨ op = .ne))) := by
  simp only [Core.tyExpr] at source
  obtain ⟨leftTy, leftFinish, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨rightTy, rightFinish, rightSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  cases leftTy with
  | int leftInt =>
    cases rightTy with
    | int rightInt =>
      by_cases equal : leftInt = rightInt
      · subst rightInt
        simp only [ite_true] at source
        have result := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
        exact ⟨.int leftInt, .int leftInt, leftFinish, rightFinish, leftSource, rightSource,
          result, Or.inl ⟨leftInt, rfl, rfl⟩⟩
      · simp only [equal] at source
        change ((rej .type "compared integers of different types" : Core.T Unit) >>=
          fun _ => pure .bool) rightFinish = .ok (ty, finish) at source
        obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
        exact (rej_ok _ _ _ _).mp rejected |>.elim
    | _ => exact (rej_ok _ _ _ _).mp source |>.elim
  | bool =>
    cases rightTy with
    | bool =>
      cases op with
      | eq | ne =>
        have result := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
        exact ⟨.bool, .bool, leftFinish, rightFinish, leftSource, rightSource,
          result, Or.inr ⟨rfl, rfl, by simp⟩⟩
      | _ => exact (rej_ok _ _ _ _).mp source |>.elim
    | _ => exact (rej_ok _ _ _ _).mp source |>.elim
  | _ => cases rightTy <;> exact (rej_ok _ _ _ _).mp source |>.elim

theorem tyExpr_pop_owner {env : Core.TEnv} {owner : Place} {origin : OriginId}
    {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.pop owner origin) start = .ok (ty, finish)) :
    ∃ info ownerStart ownerFinish, Core.tyPlace env owner ownerStart = .ok (info, ownerFinish) ∧
      info.ty.ownerElem? = some ty := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, ownerStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨info, ownerFinish, ownerSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨element, _, elementSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  have ownerElement := ownerElement_ok _ _ _ _ _ elementSource
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  have result := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
  change ty = element at result
  exact ⟨info, ownerStart, ownerFinish, ownerSource, by rw [result]; exact ownerElement.2.1⟩

theorem tyExpr_push_children {env : Core.TEnv} {owner : Place} {expr : Expr} {origin : Option OriginId}
    {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.push owner expr origin) start = .ok (ty, finish)) :
    ∃ info element ownerStart ownerFinish childStart childFinish,
      Core.tyPlace env owner ownerStart = .ok (info, ownerFinish) ∧
      info.ty.ownerElem? = some element ∧ Core.tyExpr env expr childStart = .ok (element, childFinish) ∧
      ty = .ref .mutable element := by
  have solve : ∀ ownerStart, (do
      let info ← Core.tyPlace env owner
      let element ← ownerElement env info.ty
      let argTy ← Core.tyExpr env expr
      unless argTy == element do rej .type "a pushed element of another type than the array's"
      requireWrite "push" (info.ownerMutationWritable env.mod.profile)
      pure (Ty.ref .mutable element)) ownerStart = .ok (ty, finish) →
      ∃ info element ownerStart ownerFinish childStart childFinish,
        Core.tyPlace env owner ownerStart = .ok (info, ownerFinish) ∧
        info.ty.ownerElem? = some element ∧ Core.tyExpr env expr childStart = .ok (element, childFinish) ∧
        ty = .ref .mutable element := by
    intro ownerStart source
    obtain ⟨info, ownerFinish, ownerSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨element, childStart, elementSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    have ownerElement := ownerElement_ok _ _ _ _ _ elementSource
    obtain ⟨argTy, childFinish, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    by_cases equal : (argTy == element) = true
    · simp only [equal, ite_true] at source
      have same := eq_of_beq equal
      subst argTy
      obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
      have result := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      exact ⟨info, element, ownerStart, ownerFinish, childStart, childFinish,
        ownerSource, ownerElement.2.1, childSource, result⟩
    · simp only [equal] at source
      obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
      exact (rej_ok _ _ _ _).mp rejected |>.elim
  simp only [Core.tyExpr] at source
  cases profile : env.mod.profile <;> cases origin with
  | none =>
    simp only [profile] at source solve
    first
    | exact solve start source
    | (obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
       exact (rej_ok _ _ _ _).mp rejected |>.elim)
  | some origin =>
    simp only [profile] at source solve
    obtain ⟨_, ownerStart, initial, source⟩ := (st_bind_ok _ _ _ _).mp source
    first
    | exact solve ownerStart source
    | exact (rej_ok _ _ _ _).mp initial |>.elim

end Goose.Lower.Validation
