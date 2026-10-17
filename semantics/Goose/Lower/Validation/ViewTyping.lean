import Goose.Lower.Validation.DereferenceTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerView_of_typed_of_place {env : Core.TEnv} {place : Place} {info : PlaceInfo}
    {element : Ty} {writable : Bool} {start placeFinish finish : Nat}
    (placeSource : Core.tyPlace env place start = .ok (info, placeFinish))
    (source : Core.tyView env (.of place) start = .ok ((element, writable), finish))
    {vars : Array LocalVar} {results : List Ty} {before mid : LS} {value : ValueId}
    {mu : Mutability} {block : BlockId}
    (placeRun : lowerPlace place (lowerEnv env.mod vars results) before = (value, mid))
    (placeTyped : mid.vals[value]? = some (some (.data (.ref mu info.ty))))
    (live : mid.cur = some block) :
    let (result, after) := lowerView (.of place) (lowerEnv env.mod vars results) before
    ∃ resultMu, after.cur = mid.cur ∧ after.vals[result]? = some (some (.view resultMu element)) := by
  simp only [Core.tyView] at source
  obtain ⟨sourceInfo, next, child, source⟩ := (st_bind_ok _ _ _ _).mp source
  rw [placeSource] at child
  cases Except.ok.inj child
  have operation : ∃ resultMu,
      (Op.snapshot (match place with | .var _ | .global _ => .owner | _ => .borrowed) value).resultTy
        (tyEnv (lowerEnv env.mod vars results) mid) = .ok (.view resultMu element) := by
    cases ownerTy : info.ty <;> simp only [ownerTy] at source
    all_goals try exact (rej_ok _ _ _ _).mp source |>.elim
    all_goals
      have pair := (st_pure_ok _ _ _).mp source
      have elementShape := congrArg (fun pair => pair.1.1) pair
      dsimp only at elementShape
      rw [elementShape]
      simp only [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, placeTyped,
        ownerTy, arrayElem?, pure, Except.pure, bind, Except.bind]
      exact ⟨_, rfl⟩
  obtain ⟨resultMu, operation⟩ := operation
  simp only [lowerView, bind_run, placeRun]
  have emitted := emitDef_recorded live operation
  exact ⟨resultMu, emitted.2.1, emitted.2.2.1⟩

theorem lowerView_val_typed_of_expr {env : Core.TEnv} {expr : Expr} {element : Ty}
    {sourceElement : Ty} {mu : Mutability} {writable : Bool} {start childFinish finish : Nat}
    (childSource : Core.tyExpr env expr start = .ok (.slice mu sourceElement, childFinish))
    (source : Core.tyView env (.val expr) start = .ok ((element, writable), finish))
    {vars : Array LocalVar} {results : List Ty} {before mid : LS} {value : ValueId}
    {block : BlockId} (childRun : lowerExpr expr (lowerEnv env.mod vars results) before = (value, mid))
    (childTyped : mid.vals[value]? = some (some (.data (.slice mu sourceElement))))
    (live : mid.cur = some block) :
    let (result, after) := lowerView (.val expr) (lowerEnv env.mod vars results) before
    after.cur = mid.cur ∧ after.vals[result]? = some (some (.view mu element)) := by
  simp only [Core.tyView] at source
  obtain ⟨childTy, next, child, source⟩ := (st_bind_ok _ _ _ _).mp source
  rw [childSource] at child
  cases Except.ok.inj child
  have pair := (st_pure_ok _ _ _).mp source
  have elementShape : element = sourceElement := congrArg (fun pair => pair.1.1) pair
  have emitted := sliceView_typed (le := lowerEnv env.mod vars results) childTyped live
  simpa only [lowerView, bind_run, childRun, elementShape] using emitted

theorem lowerPlace_elem_typed_of_children {le : LEnv} {view : View} {index : Expr}
    {origin : OriginId} {element : Ty} {mu : Mutability} {intTy : IntTy}
    {before viewState mid : LS} {viewValue indexValue : ValueId} {block : BlockId}
    (viewRun : lowerView view le before = (viewValue, viewState))
    (viewTyped : viewState.vals[viewValue]? = some (some (.view mu element)))
    (indexRun : lowerExpr index le viewState = (indexValue, mid))
    (indexTyped : mid.vals[indexValue]? = some (some (.data (.int intTy))))
    (live : mid.cur = some block) :
    let (result, after) := lowerPlace (.elem view index origin) le before
    after.cur = mid.cur ∧ after.vals[result]? = some (some (.data (.ref mu element))) := by
  have retained := types_lowerExpr index le viewState indexValue mid indexRun viewValue (.view mu element) viewTyped
  have operation : (Op.indexChecked viewValue indexValue (some origin)).resultTy (tyEnv le mid) =
      .ok (.data (.ref mu element)) := by
    simp [Op.resultTy, TyEnv.viewTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
      retained, indexTyped, pure, Except.pure, bind, Except.bind]
  simp only [lowerPlace, bind_run, viewRun, indexRun]
  have emitted := emitDef_recorded live operation
  exact ⟨emitted.2.1, emitted.2.2.1⟩

theorem tyPlace_elem_children {env : Core.TEnv} {view : View} {index : Expr} {origin : OriginId}
    {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env (.elem view index origin) start = .ok (info, finish)) :
    ∃ viewStart viewFinish indexFinish writable intTy,
      Core.tyView env view viewStart = .ok ((info.ty, writable), viewFinish) ∧
      Core.tyExpr env index viewFinish = .ok (.int intTy, indexFinish) := by
  simp only [Core.tyPlace] at source
  obtain ⟨_, viewStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨pair, viewFinish, viewTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨indexTy, indexFinish, indexTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨intTy, afterInt, intChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
  have integer := (requireInt_ok _ _ _ _).mp intChecked
  rw [integer.1] at indexTyped
  have result := (st_pure_ok _ _ _).mp source
  have elementShape : info.ty = pair.1 := congrArg (fun pair => pair.1.ty) result
  exact ⟨viewStart, viewFinish, indexFinish, pair.2, intTy,
    by simpa only [elementShape] using viewTyped, indexTyped⟩

end Goose.Lower.Validation
