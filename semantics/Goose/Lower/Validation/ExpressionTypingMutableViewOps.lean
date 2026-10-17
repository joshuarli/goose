import Goose.Lower.Validation.ExpressionTypingMutableDerefOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem tyView_val_writable_child {env : Core.TEnv} {expr : Expr} {element : Ty} {start finish : Nat}
    (source : Core.tyView env (.val expr) start = .ok ((element, true), finish)) :
    ∃ childFinish, Core.tyExpr env expr start = .ok (.slice .mutable element, childFinish) := by
  simp only [Core.tyView] at source
  obtain ⟨ty, next, child, source⟩ := (st_bind_ok _ _ _ _).mp source
  cases ty with
  | slice mu target =>
    have pair := (st_pure_ok _ _ _).mp source
    have shape := congrArg Prod.fst pair
    dsimp only at shape
    have referent := congrArg Prod.fst shape
    have writable := congrArg Prod.snd shape
    dsimp only at referent writable
    cases mu with
    | readOnly => simp at writable
    | mutable => exact ⟨next, by simpa only [← referent] using child⟩
  | _ => exact (rej_ok _ _ _ _).mp source |>.elim

theorem tyExpr_slice_mutable_children {env : Core.TEnv} {view : View} {lo hi : Bound}
    {origin : OriginId} {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.slice .mutable view lo hi origin) start = .ok (ty, finish)) :
    ∃ element viewStart viewFinish lowFinish highFinish,
      Core.tyView env view viewStart = .ok ((element, true), viewFinish) ∧
      Core.tyBound env lo viewFinish = .ok ((), lowFinish) ∧
      Core.tyBound env hi lowFinish = .ok ((), highFinish) ∧ ty = .slice .mutable element := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, viewStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨pair, viewFinish, viewSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, lowFinish, lowSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, highFinish, highSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, permission, source⟩ := (st_bind_ok _ _ _ _).mp source
  have writable := (requireWrite_ok _ _ _ _).mp permission
  have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
  refine ⟨pair.1, viewStart, viewFinish, lowFinish, highFinish, ?_, lowSource, highSource, shape⟩
  have pairShape : pair = (pair.1, true) := Prod.ext rfl writable.1
  rw [← pairShape]
  exact viewSource

theorem mutableSlice_resultTy {le : LEnv} {state : LS} {view : ValueId}
    {element : Ty} {lo hi : Bnd}
    (typed : state.vals[view]? = some (some (.view .mutable element)))
    (low : BoundTyped state lo) (high : BoundTyped state hi) (origin : OriginId) :
    (Op.viewSlice .mutable view lo hi (some origin)).resultTy (tyEnv le state) =
      .ok (.data (.slice .mutable element)) := by
  have lowCheck := low.check (le := le)
  have highCheck := high.check (le := le)
  have viewCheck : (tyEnv le state).viewTy view = .ok (.mutable, element) := by
    simp [TyEnv.viewTy, TyEnv.valTy, tyEnv, typed, pure, Except.pure, bind, Except.bind]
  simp only [Op.resultTy, viewCheck, Mutability.atLeast, ite_true, lowCheck, highCheck,
    pure, Except.pure, bind, Except.bind]

theorem lowerView_val_writable_typed_of_child {env : Core.TEnv} {expr : Expr} {element : Ty}
    {start finish : Nat} (source : Core.tyView env (.val expr) start = .ok ((element, true), finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerView (.val expr) (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (childTyped : ∀ childFinish childState childValue,
      Core.tyExpr env expr start = .ok (.slice .mutable element, childFinish) →
      lowerExpr expr (lowerEnv env.mod env.vars results) before = (childValue, childState) →
      childState.cur.isSome = true → childState.vals[childValue]? = some (some (.data (.slice .mutable element)))) :
    after.vals[value]? = some (some (.view .mutable element)) := by
  obtain ⟨childFinish, childSource⟩ := tyView_val_writable_child source
  have lowering := run
  simp only [lowerView] at lowering
  obtain ⟨childValue, childState, childRun, emitted⟩ := bind_eq.mp lowering
  have childLive := (dead_emitDef (.sliceView childValue)).live_before emitted live
  have typed := childTyped childFinish childState childValue childSource childRun childLive
  cases current : childState.cur with
  | none => simp [current] at childLive
  | some block =>
    have lowered := lowerView_val_typed_of_expr childSource source childRun typed current
    rw [run] at lowered
    exact lowered.2

end Goose.Lower.Validation
