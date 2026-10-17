import Goose.Lower.Validation.BuilderTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerExpr_un_typed_of_child {le : LEnv} {before mid : LS} {expr : Expr}
    {value : ValueId} {ty : IntTy} {op : UnOp} {origin : OriginId} {block : BlockId}
    (childRun : lowerExpr expr le before = (value, mid))
    (typed : mid.vals[value]? = some (some (.data (.int ty))))
    (signed : op = .neg → ty.signed = true) (live : mid.cur = some block) :
    let (result, after) := lowerExpr (.un op expr origin) le before
    after.cur = mid.cur ∧ after.vals[result]? = some (some (.data (.int ty))) := by
  have integer := intTyOf_recorded (le := le) typed
  have operation : (Op.un op ty value (some origin)).resultTy (tyEnv le mid) = .ok (.data (.int ty)) := by
    cases op with
    | neg => simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
        typed, signed rfl, pure, Except.pure, bind, Except.bind]
    | bitnot => simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
        typed, pure, Except.pure, bind, Except.bind]
  simp only [lowerExpr, bind_run, childRun, integer]
  have emitted := emitDef_recorded live operation
  exact ⟨emitted.2.1, emitted.2.2.1⟩

theorem lowerExpr_bin_typed_of_children {le : LEnv} {before leftState mid : LS}
    {left right : Expr} {leftValue rightValue : ValueId} {ty : IntTy}
    {op : BinOp} {origin : OriginId} {block : BlockId}
    (leftRun : lowerExpr left le before = (leftValue, leftState))
    (leftTyped : leftState.vals[leftValue]? = some (some (.data (.int ty))))
    (rightRun : lowerExpr right le leftState = (rightValue, mid))
    (rightTyped : mid.vals[rightValue]? = some (some (.data (.int ty))))
    (live : mid.cur = some block) :
    let (result, after) := lowerExpr (.bin op left right origin) le before
    after.cur = mid.cur ∧ after.vals[result]? = some (some (.data (.int ty))) := by
  have retained := types_lowerExpr right le leftState rightValue mid rightRun leftValue (.data (.int ty)) leftTyped
  have integer := intTyOf_recorded (le := le) retained
  have operation : (Op.bin op ty leftValue rightValue (some origin)).resultTy (tyEnv le mid) =
      .ok (.data (.int ty)) := by
    simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
      retained, rightTyped, pure, Except.pure, bind, Except.bind]
  simp only [lowerExpr, bind_run, leftRun, rightRun, integer]
  have emitted := emitDef_recorded live operation
  exact ⟨emitted.2.1, emitted.2.2.1⟩

theorem lowerExpr_not_typed_of_child {le : LEnv} {before mid : LS} {expr : Expr}
    {value : ValueId} {block : BlockId} (childRun : lowerExpr expr le before = (value, mid))
    (typed : mid.vals[value]? = some (some (.data .bool))) (live : mid.cur = some block) :
    let (result, after) := lowerExpr (.not expr) le before
    after.cur = mid.cur ∧ after.vals[result]? = some (some (.data .bool)) := by
  have operation : (Op.boolNot value).resultTy (tyEnv le mid) = .ok (.data .bool) := by
    simp [Op.resultTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, typed, pure, Except.pure, bind, Except.bind]
  simp only [lowerExpr, bind_run, childRun]
  have emitted := emitDef_recorded live operation
  exact ⟨emitted.2.1, emitted.2.2.1⟩

theorem tyExpr_un_child {env : Core.TEnv} {expr : Expr} {op : UnOp} {origin : OriginId}
    {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.un op expr origin) start = .ok (ty, finish)) :
    ∃ childStart childFinish intTy, Core.tyExpr env expr childStart = .ok (.int intTy, childFinish) ∧
      ty = .int intTy ∧ (op = .neg → intTy.signed = true) := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, childStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨childTy, childFinish, childTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨intTy, afterInt, intChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
  have childShape := (requireInt_ok _ _ _ _).mp intChecked
  rw [childShape.1] at childTyped
  refine ⟨childStart, childFinish, intTy, childTyped, ?_, ?_⟩
  · cases op with
    | neg =>
      by_cases signed : intTy.signed = true
      · simp only [signed, ite_true] at source
        exact congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      · simp [signed, chk] at source
    | bitnot => exact congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
  · intro negative
    subst op
    by_cases signed : intTy.signed = true
    · exact signed
    · simp [signed, chk] at source

theorem tyExpr_bin_children {env : Core.TEnv} {left right : Expr} {op : BinOp} {origin : OriginId}
    {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.bin op left right origin) start = .ok (ty, finish)) :
    ∃ leftStart leftFinish rightStart rightFinish intTy,
      Core.tyExpr env left leftStart = .ok (.int intTy, leftFinish) ∧
      Core.tyExpr env right rightStart = .ok (.int intTy, rightFinish) ∧ ty = .int intTy := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, leftStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨leftTy, leftFinish, leftTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨leftInt, rightStart, leftInteger, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨rightTy, rightFinish, rightTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨rightInt, afterInt, rightInteger, source⟩ := (st_bind_ok _ _ _ _).mp source
  have leftShape := (requireInt_ok _ _ _ _).mp leftInteger
  have rightShape := (requireInt_ok _ _ _ _).mp rightInteger
  rw [leftShape.1] at leftTyped
  rw [rightShape.1] at rightTyped
  by_cases equal : leftInt = rightInt
  · subst rightInt
    simp only [ite_true] at source
    exact ⟨leftStart, leftFinish, rightStart, rightFinish, leftInt, leftTyped, rightTyped,
      congrArg Prod.fst ((st_pure_ok _ _ _).mp source)⟩
  · simp only [equal, ite_false] at source
    obtain ⟨_, _, impossible, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact (rej_ok _ _ _ _).mp impossible |>.elim

theorem tyExpr_not_child {env : Core.TEnv} {expr : Expr} {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.not expr) start = .ok (ty, finish)) :
    ∃ childFinish, Core.tyExpr env expr start = .ok (.bool, childFinish) ∧ ty = .bool := by
  simp only [Core.tyExpr] at source
  obtain ⟨childTy, childFinish, childTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, afterBool, boolean, source⟩ := (st_bind_ok _ _ _ _).mp source
  have childShape := (requireBool_ok _ _ _ _).mp boolean
  rw [childShape.1] at childTyped
  exact ⟨childFinish, childTyped, congrArg Prod.fst ((st_pure_ok _ _ _).mp source)⟩

end Goose.Lower.Validation
