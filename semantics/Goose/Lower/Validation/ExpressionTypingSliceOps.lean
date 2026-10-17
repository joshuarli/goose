import Goose.Lower.Validation.ExpressionTypingScalarOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

def BoundTyped (state : LS) : Bnd → Prop
  | .omitted => True
  | .val value | .fromEnd value => ∃ intTy, state.vals[value]? = some (some (.data (.int intTy)))

theorem BoundTyped.retained {before after : LS} {bound : Bnd}
    (typed : BoundTyped before bound) (retained : TypePrefix before after) : BoundTyped after bound := by
  cases bound with
  | omitted => trivial
  | val value | fromEnd value =>
    obtain ⟨intTy, typed⟩ := typed
    exact ⟨intTy, retained value (.data (.int intTy)) typed⟩

theorem BoundTyped.check {le : LEnv} {state : LS} {bound : Bnd} (typed : BoundTyped state bound) :
    (tyEnv le state).boundTy bound = .ok () := by
  cases bound with
  | omitted => rfl
  | val value | fromEnd value =>
    obtain ⟨intTy, typed⟩ := typed
    simp [TyEnv.boundTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
      typed, pure, Except.pure, bind, Except.bind]

theorem readonlySlice_resultTy {le : LEnv} {state : LS} {view : ValueId} {actual : Mutability}
    {element : Ty} {lo hi : Bnd}
    (typed : state.vals[view]? = some (some (.view actual element)))
    (low : BoundTyped state lo) (high : BoundTyped state hi) (origin : OriginId) :
    (Op.viewSlice .readOnly view lo hi (some origin)).resultTy (tyEnv le state) =
      .ok (.data (.slice .readOnly element)) := by
  have permission : actual.atLeast .readOnly = true := by cases actual <;> rfl
  have lowCheck := low.check (le := le)
  have highCheck := high.check (le := le)
  simp only [Op.resultTy]
  have viewCheck : (tyEnv le state).viewTy view = .ok (actual, element) := by
    simp [TyEnv.viewTy, TyEnv.valTy, tyEnv, typed, pure, Except.pure, bind, Except.bind]
  rw [viewCheck]
  simp only [permission, ite_true, lowCheck, highCheck, pure, Except.pure, bind, Except.bind]

theorem tyExpr_slice_children {env : Core.TEnv} {mu : Mutability} {view : View} {lo hi : Bound}
    {origin : OriginId} {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.slice mu view lo hi origin) start = .ok (ty, finish)) :
    ∃ element writable viewStart viewFinish lowFinish highFinish,
      Core.tyView env view viewStart = .ok ((element, writable), viewFinish) ∧
      Core.tyBound env lo viewFinish = .ok ((), lowFinish) ∧
      Core.tyBound env hi lowFinish = .ok ((), highFinish) ∧ ty = .slice mu element := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, viewStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨pair, viewFinish, viewSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, lowFinish, lowSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, highFinish, highSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  cases mu with
  | readOnly =>
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    exact ⟨pair.1, pair.2, viewStart, viewFinish, lowFinish, highFinish,
      viewSource, lowSource, highSource, shape⟩
  | mutable =>
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    exact ⟨pair.1, pair.2, viewStart, viewFinish, lowFinish, highFinish,
      viewSource, lowSource, highSource, shape⟩

theorem tyBound_child {env : Core.TEnv} {expr : Expr} {start finish : Nat}
    (source : (do let _ ← requireInt "a slice bound" (← Core.tyExpr env expr)) start = .ok ((), finish)) :
    ∃ intTy childFinish, Core.tyExpr env expr start = .ok (.int intTy, childFinish) := by
  obtain ⟨ty, childFinish, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨intTy, next, integerSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  have integer := (requireInt_ok _ _ _ _).mp integerSource
  exact ⟨_, childFinish, by simpa only [integer.1] using childSource⟩

end Goose.Lower.Validation
