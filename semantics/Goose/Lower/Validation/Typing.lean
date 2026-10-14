import Goose.Lower.Validate
import Goose.Core.Sound.Check

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem emitDef_recorded {le : LEnv} {before : LS} {block : BlockId}
    {op : Op} {ty : VTy} (live : before.cur = some block)
    (typed : op.resultTy (tyEnv le before) = .ok ty) :
    let (value, after) := emitDef op le before
    value = before.vals.size ∧ after.cur = before.cur ∧
      after.vals[value]? = some (some ty) ∧
      (∀ old, old < before.vals.size → after.vals[old]? = before.vals[old]?) := by
  rw [emitDef_run op le live]
  simp only [typed, Except.toOption, Option.getD_some]
  refine ⟨True.intro, True.intro, ?_, ?_⟩
  · simp
  · intro old bound
    simp [Array.getElem?_push, bound, Nat.ne_of_lt bound]

theorem valTy_of_recorded {le : LEnv} {state : LS} {value : ValueId} {ty : VTy}
    (typed : state.vals[value]? = some (some ty)) :
    valTy value le state = (ty, state) := by
  simp [valTy, bind_run, typed, pure_run]

theorem emitDef_result_reference {le : LEnv} {before : LS} {block : BlockId}
    {op : Op} {ty : Ty} {mu : Mutability} (live : before.cur = some block)
    (typed : op.resultTy (tyEnv le before) = .ok (.data (.ref mu ty))) :
    let (value, after) := emitDef op le before
    after.vals[value]? = some (some (.data (.ref mu ty))) :=
  (emitDef_recorded live typed).2.2.1

theorem lowerExpr_literal_typed {env : Core.TEnv} {intTy : IntTy} {number : Int}
    {sourceTy : Ty} {next final : Nat}
    (source : Core.tyExpr env (.lit intTy number) next = .ok (sourceTy, final))
    (le : LEnv) (before : LS) {block : BlockId} (live : before.cur = some block) :
    let (value, after) := lowerExpr (.lit intTy number) le before
    sourceTy = .int intTy ∧ after.cur = before.cur ∧
      after.vals[value]? = some (some (.data sourceTy)) := by
  by_cases range : intTy.inRange number
  · have shape : sourceTy = .int intTy := by
      have pair : (.int intTy, next) = (sourceTy, final) := by
        simpa [Core.tyExpr, range, pure, StateT.pure, Except.pure] using source
      exact (congrArg Prod.fst pair).symm
    subst sourceTy
    have typed : (Op.constInt intTy number).resultTy (tyEnv le before) =
        .ok (.data (.int intTy)) := by simp [Op.resultTy, range, pure, Except.pure]
    have result := emitDef_recorded live typed
    exact ⟨rfl, result.2.1, result.2.2.1⟩
  · simp only [Core.tyExpr, range] at source
    change Except.error _ = Except.ok _ at source
    cases source

theorem lowerExpr_bool_typed (value : Bool) (le : LEnv) (before : LS)
    {block : BlockId} (live : before.cur = some block) :
    let (result, after) := lowerExpr (.bool value) le before
    after.cur = before.cur ∧ after.vals[result]? = some (some (.data .bool)) := by
  have typed : (Op.constBool value).resultTy (tyEnv le before) = .ok (.data .bool) := rfl
  have result := emitDef_recorded live typed
  exact ⟨result.2.1, result.2.2.1⟩

theorem lowerExpr_read_typed_of_place {le : LEnv} {before mid : LS}
    {place : Place} {reference : ValueId} {mu : Mutability} {ty : Ty} {block : BlockId}
    (placeRun : lowerPlace place le before = (reference, mid))
    (placeType : mid.vals[reference]? = some (some (.data (.ref mu ty))))
    (live : mid.cur = some block) :
    let (value, after) := lowerExpr (.read place) le before
    after.cur = mid.cur ∧ after.vals[value]? = some (some (.data ty)) := by
  have typed : (Op.load reference).resultTy (tyEnv le mid) = .ok (.data ty) := by
    simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, placeType, pure, Except.pure, bind, Except.bind]
  simp only [lowerExpr, bind_run, placeRun]
  have result := emitDef_recorded live typed
  exact ⟨result.2.1, result.2.2.1⟩

theorem lowerPlace_var_typed {env : Core.TEnv} {varId : VarId}
    {info : PlaceInfo} {next final : Nat}
    (source : Core.tyPlace env (.var varId) next = .ok (info, final))
    (results : List Ty) (before : LS) {block : BlockId} (live : before.cur = some block) :
    let (value, after) := lowerPlace (.var varId) (lowerEnv env.mod env.vars results) before
    ∃ mu, after.cur = before.cur ∧
      after.vals[value]? = some (some (.data (.ref mu info.ty))) := by
  simp only [Core.tyPlace] at source
  obtain ⟨localVar, intermediate, lookup, shape⟩ :=
    (Core.Sound.st_bind_ok _ _ _ _).mp source
  have varIdRow := (Core.Sound.varOf_ok _ _ _ _).mp lookup
  have pair := (Core.Sound.st_pure_ok _ _ _).mp shape
  have referent : info.ty = localVar.ty := by
    exact congrArg (fun pair => pair.1.ty) pair
  have slotRow : (lowerEnv env.mod env.vars results).slots[varId]? =
      some ⟨localVar.ty, localVar.kind, localVar.scope, varId⟩ := by
    simp [lowerEnv, Array.getElem?_mapIdx, varIdRow.2.1]
  have address : ∃ mu, (Op.slotAddr varId).resultTy
      (tyEnv (lowerEnv env.mod env.vars results) before) = .ok (.data (.ref mu info.ty)) := by
    simp only [Op.resultTy, tyEnv, slotRow]
    rw [referent]
    exact ⟨_, rfl⟩
  obtain ⟨mu, address⟩ := address
  have emitted := emitDef_recorded live address
  exact ⟨mu, emitted.2.1, emitted.2.2.1⟩

theorem lowerPlace_global_typed {env : Core.TEnv} {global : GlobalId}
    {info : PlaceInfo} {next final : Nat}
    (source : Core.tyPlace env (.global global) next = .ok (info, final))
    (vars : Array LocalVar) (results : List Ty) (before : LS) {block : BlockId} (live : before.cur = some block) :
    let (value, after) := lowerPlace (.global global) (lowerEnv env.mod vars results) before
    ∃ mu, after.cur = before.cur ∧
      after.vals[value]? = some (some (.data (.ref mu info.ty))) := by
  by_cases available : global < env.globalLimit
  · cases globalRow : env.mod.globals[global]? with
    | none =>
      simp only [Core.tyPlace, available, ↓reduceIte, globalRow] at source
      change Except.error _ = Except.ok _ at source
      cases source
    | some globalVar =>
      simp only [Core.tyPlace, available, ↓reduceIte, globalRow] at source
      have pair := (Core.Sound.st_pure_ok _ _ _).mp source
      have referent : info.ty = globalVar.ty := congrArg (fun pair => pair.1.ty) pair
      have address : ∃ mu, (Op.globalAddr global).resultTy
          (tyEnv (lowerEnv env.mod vars results) before) = .ok (.data (.ref mu info.ty)) := by
        simp only [Op.resultTy, tyEnv, lowerEnv, Array.getElem?_map, globalRow, Option.map_some]
        rw [referent]
        exact ⟨_, rfl⟩
      obtain ⟨mu, address⟩ := address
      have emitted := emitDef_recorded live address
      exact ⟨mu, emitted.2.1, emitted.2.2.1⟩
  · simp only [Core.tyPlace, available, ↓reduceIte] at source
    change Except.error _ = Except.ok _ at source
    cases source

theorem pushParamTypes_preserves_lookup (types : List VTy) (values : Array (Option VTy))
    (index : Nat) (bound : index < values.size) :
    (pushParamTypes types values)[index]? = values[index]? := by
  induction types generalizing values with
  | nil => rfl
  | cons ty types inductionHypothesis =>
    change (pushParamTypes types (values.push (some ty)))[index]? = values[index]?
    rw [inductionHypothesis (values.push (some ty)) (by simp; omega)]
    simp [Array.getElem?_push, bound, Nat.ne_of_lt bound]

theorem pushParamTypes_lookup (types : List VTy) (values : Array (Option VTy)) (index : Nat) :
    (pushParamTypes types values)[values.size + index]? = types[index]?.map some := by
  induction types generalizing values index with
  | nil =>
    simp only [pushParamTypes, List.foldl_nil, List.getElem?_nil, Option.map_none]
    exact Array.getElem?_eq_none (by omega)
  | cons ty types inductionHypothesis =>
    cases index with
    | zero =>
      change (pushParamTypes types (values.push (some ty)))[values.size]? = some (some ty)
      rw [pushParamTypes_preserves_lookup _ _ _ (by simp)]
      simp
    | succ index =>
      change (pushParamTypes types (values.push (some ty)))[values.size + (index + 1)]? =
        types[index]?.map some
      have indexEquality : values.size + (index + 1) = (values.push (some ty)).size + index := by
        simp
        omega
      rw [indexEquality]
      exact inductionHypothesis (values.push (some ty)) index

theorem newBlock_parameter_types (types : List VTy) (le : LEnv) (before : LS) (index : Nat) :
    (newBlock types le before).2.vals[before.vals.size + index]? = types[index]?.map some :=
  pushParamTypes_lookup types before.vals index

theorem intTyOf_recorded {le : LEnv} {before : LS} {value : ValueId} {ty : IntTy}
    (typed : before.vals[value]? = some (some (.data (.int ty)))) :
    intTyOf value le before = (ty, before) := by
  simp only [intTyOf, bind_run, valTy_of_recorded typed, pure_run]

theorem freezeTo_typed {le : LEnv} {before : LS} {value : ValueId} {ty : Ty}
    {actual requested : Mutability} {block : BlockId}
    (typed : before.vals[value]? = some (some (.data (.ref actual ty))))
    (permission : actual.atLeast requested = true) (live : before.cur = some block) :
    let (result, after) := freezeTo requested value le before
    after.cur = before.cur ∧ after.vals[result]? = some (some (.data (.ref requested ty))) := by
  cases requested <;> cases actual
  · simpa only [freezeTo, bind_run, valTy_of_recorded typed, pure_run] using
      And.intro (Eq.refl before.cur) typed
  · simp [Mutability.atLeast] at permission
  · have freezeTyped : (Op.refFreeze value).resultTy (tyEnv le before) =
        .ok (.data (.ref .readOnly ty)) := by
      simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
        typed, pure, Except.pure, bind, Except.bind]
    simp only [freezeTo, bind_run, valTy_of_recorded typed]
    exact ⟨(emitDef_recorded live freezeTyped).2.1,
      (emitDef_recorded live freezeTyped).2.2.1⟩
  · simpa only [freezeTo, bind_run, valTy_of_recorded typed, pure_run] using
      And.intro (Eq.refl before.cur) typed

theorem sliceView_typed {le : LEnv} {before : LS} {value : ValueId} {element : Ty}
    {mu : Mutability} {block : BlockId}
    (typed : before.vals[value]? = some (some (.data (.slice mu element))))
    (live : before.cur = some block) :
    let (result, after) := emitDef (.sliceView value) le before
    after.cur = before.cur ∧ after.vals[result]? = some (some (.view mu element)) := by
  have viewTyped : (Op.sliceView value).resultTy (tyEnv le before) =
      .ok (.view mu element) := by
    simp [Op.resultTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
      typed, pure, Except.pure, bind, Except.bind]
  have emitted := emitDef_recorded live viewTyped
  exact ⟨emitted.2.1, emitted.2.2.1⟩

theorem readonlySlice_typed {le : LEnv} {before : LS} {view : ValueId} {element : Ty}
    {mu : Mutability} {block : BlockId}
    (typed : before.vals[view]? = some (some (.view mu element)))
    (live : before.cur = some block) (origin : OriginId) :
    let (result, after) := emitDef (.viewSlice .readOnly view .omitted .omitted (some origin)) le before
    after.cur = before.cur ∧ after.vals[result]? = some (some (.data (.slice .readOnly element))) := by
  have permission : mu.atLeast .readOnly = true := by cases mu <;> rfl
  have sliceTyped : (Op.viewSlice .readOnly view .omitted .omitted (some origin)).resultTy
      (tyEnv le before) = .ok (.data (.slice .readOnly element)) := by
    simp [Op.resultTy, TyEnv.viewTy, TyEnv.valTy, TyEnv.boundTy, tyEnv,
      typed, permission, pure, Except.pure, bind, Except.bind]
  have emitted := emitDef_recorded live sliceTyped
  exact ⟨emitted.2.1, emitted.2.2.1⟩

end Goose.Lower.Validation
