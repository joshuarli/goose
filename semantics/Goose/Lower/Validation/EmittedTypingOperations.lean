import Goose.Lower.Validation.EmittedTypingBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_constInt (le : LEnv) (before : LS) (type : IntTy) (value : Int)
    (range : type.inRange value = true) : EmittedAt le before (emitDef (.constInt type value)) := by
  exact .emit .refl _ (.data (.int type)) (by simp [Op.resultTy, range, pure, Except.pure])

theorem emitted_constBool (le : LEnv) (before : LS) (value : Bool) :
    EmittedAt le before (emitDef (.constBool value)) := .emit .refl _ _ rfl

theorem emitted_constUnit (le : LEnv) (before : LS) :
    EmittedAt le before (emitDef .constUnit) := .emit .refl _ _ rfl

theorem emitted_load {le : LEnv} {before : LS} {value : ValueId} {mu : Mutability} {type : Ty}
    (typed : before.vals[value]? = some (some (.data (.ref mu type)))) :
    EmittedAt le before (emitDef (.load value)) := by
  exact .emit .refl _ (.data type) (by
    simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, typed,
      pure, Except.pure, bind, Except.bind])

theorem emitted_refFreeze {le : LEnv} {before : LS} {value : ValueId} {mu : Mutability} {type : Ty}
    (typed : before.vals[value]? = some (some (.data (.ref mu type)))) :
    EmittedAt le before (emitDef (.refFreeze value)) := by
  exact .emit .refl _ (.data (.ref .readOnly type)) (by
    simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, typed,
      pure, Except.pure, bind, Except.bind])

theorem emitted_boolNot {le : LEnv} {before : LS} {value : ValueId}
    (typed : before.vals[value]? = some (some (.data .bool))) :
    EmittedAt le before (emitDef (.boolNot value)) := by
  exact .emit .refl _ (.data .bool) (by
    simp [Op.resultTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, typed,
      pure, Except.pure, bind, Except.bind])

theorem emitted_bin {le : LEnv} {before : LS} {left right : ValueId} {type : IntTy}
    (leftTyped : before.vals[left]? = some (some (.data (.int type))))
    (rightTyped : before.vals[right]? = some (some (.data (.int type))))
    (op : BinOp) (origin : Option OriginId) : EmittedAt le before (emitDef (.bin op type left right origin)) := by
  exact .emit .refl _ (.data (.int type)) (by
    simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
      leftTyped, rightTyped, pure, Except.pure, bind, Except.bind])

theorem emitted_un {le : LEnv} {before : LS} {value : ValueId} {type : IntTy}
    (typed : before.vals[value]? = some (some (.data (.int type))))
    (op : UnOp) (signed : op = .neg → type.signed = true) (origin : Option OriginId) :
    EmittedAt le before (emitDef (.un op type value origin)) := by
  apply EmittedTrace.emit .refl _ (.data (.int type))
  cases op with
  | neg => simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
      typed, signed rfl, pure, Except.pure, bind, Except.bind]
  | bitnot => simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
      typed, pure, Except.pure, bind, Except.bind]

theorem emitted_next {le : LEnv} {before : LS} {value : ValueId} {type : IntTy}
    (typed : before.vals[value]? = some (some (.data (.int type)))) :
    EmittedAt le before (emitDef (.next type value)) := by
  exact .emit .refl _ (.data (.int type)) (by
    simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
      typed, pure, Except.pure, bind, Except.bind])

theorem emitted_viewLen {le : LEnv} {before : LS} {value : ValueId} {mu : Mutability} {type : Ty}
    (typed : before.vals[value]? = some (some (.view mu type))) :
    EmittedAt le before (emitDef (.viewLen value)) := by
  exact .emit .refl _ (.data (.int .i64)) (by
    simp [Op.resultTy, TyEnv.viewTy, TyEnv.valTy, tyEnv, typed,
      pure, Except.pure, bind, Except.bind])

theorem emitted_freezeTo (le : LEnv) (before : LS) (mu : Mutability) (value : ValueId) :
    EmittedAt le before (freezeTo mu value) := by
  cases mu <;> cases row : before.vals[value]? with
  | none => simpa only [EmittedAt, freezeTo, bind_run, valTy, get_apply, row, pure_run] using EmittedTrace.refl (le := le) (initial := before)
  | some recorded => cases recorded with
    | none => simpa only [EmittedAt, freezeTo, bind_run, valTy, get_apply, row, pure_run] using EmittedTrace.refl (le := le) (initial := before)
    | some type =>
      cases type with
      | view _ _ => simpa only [EmittedAt, freezeTo, bind_run, valTy_of_recorded row, pure_run] using EmittedTrace.refl (le := le) (initial := before)
      | data type =>
        cases type <;> first
          | (simpa only [EmittedAt, freezeTo, bind_run, valTy_of_recorded row, pure_run] using EmittedTrace.refl (le := le) (initial := before))
          | (rename_i actual target
             cases actual <;> first
               | (simpa only [EmittedAt, freezeTo, bind_run, valTy_of_recorded row, pure_run] using EmittedTrace.refl (le := le) (initial := before))
               | (simpa only [EmittedAt, freezeTo, bind_run, valTy_of_recorded row, pure_run] using emitted_refFreeze (le := le) row))

theorem emitted_sliceView {le : LEnv} {before : LS} {value : ValueId} {mu : Mutability} {type : Ty}
    (typed : before.vals[value]? = some (some (.data (.slice mu type)))) :
    EmittedAt le before (emitDef (.sliceView value)) := by
  exact .emit .refl _ (.view mu type) (by
    simp [Op.resultTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, typed,
      pure, Except.pure, bind, Except.bind])

theorem emitted_readOnlySlice {le : LEnv} {before : LS} {value : ValueId} {mu : Mutability} {type : Ty}
    (typed : before.vals[value]? = some (some (.view mu type))) (origin : OriginId) :
    EmittedAt le before (emitDef (.viewSlice .readOnly value .omitted .omitted (some origin))) := by
  have permission : mu.atLeast .readOnly = true := by cases mu <;> rfl
  exact .emit .refl _ (.data (.slice .readOnly type)) (by
    simp [Op.resultTy, TyEnv.viewTy, TyEnv.valTy, TyEnv.boundTy, tyEnv, typed, permission,
      pure, Except.pure, bind, Except.bind])

theorem emitted_valTy_nonunit {le : LEnv} {before : LS} {value : ValueId} {type : VTy}
    (nonunit : type ≠ .data .unit) (observed : (valTy value le before).1 = type) :
    before.vals[value]? = some (some type) := by
  cases row : before.vals[value]? with
  | none => simp [valTy, bind_run, row, pure_run] at observed; exact (nonunit observed.symm).elim
  | some recorded => cases recorded with
    | none => simp [valTy, bind_run, row, pure_run] at observed; exact (nonunit observed.symm).elim
    | some actual =>
      have same : actual = type := by simpa [valTy, bind_run, row, pure_run] using observed
      simpa only [same] using row

theorem emitted_coerceTo (le : LEnv) (before : LS) (target : Ty) (value : ValueId) (origin : OriginId) :
    EmittedAt le before (coerceTo target value origin) := by
  unfold coerceTo
  apply (EmittedAt.valTy le before value).bind
  rw [valTy_run]
  split
  next targetElement sourceElement observed =>
    exact emitted_refFreeze (emitted_valTy_nonunit (by intro h; cases h) observed)
  next targetElement sourceElement observed =>
    have row := emitted_valTy_nonunit (by intro h; cases h) observed
    cases live : before.cur with
    | none =>
      have dead := emitDef_none (.sliceView value) le live
      have deadNext := emitDef_none (.viewSlice .readOnly 0 .omitted .omitted (some origin)) le live
      simpa only [EmittedAt, bind_run, dead, deadNext] using EmittedTrace.refl (le := le) (initial := before)
    | some block =>
      have success : (Op.sliceView value).resultTy (tyEnv le before) = .ok (.view .mutable sourceElement) := by
        simp [Op.resultTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, row, pure, Except.pure, bind, Except.bind]
      have recorded := (emitDef_recorded live success).2.2.1
      have first := emitted_sliceView (le := le) row
      have second := emitted_readOnlySlice (le := le) recorded origin
      exact first.append second
  next => exact EmittedAt.pure _ _ _


theorem emitted_slotAddr {le : LEnv} {before : LS} {slot : SlotId} {descriptor : GIR.Slot}
    (row : le.slots[slot]? = some descriptor) : EmittedAt le before (emitDef (.slotAddr slot)) :=
  .emit .refl _ _ (by simp only [Op.resultTy, tyEnv, row]; rfl)

theorem emitted_globalAddr {le : LEnv} {before : LS} {global : GlobalId} {type : Ty} {kind : VarKind}
    (row : le.globals[global]? = some (type, kind)) : EmittedAt le before (emitDef (.globalAddr global)) :=
  .emit .refl _ _ (by simp only [Op.resultTy, tyEnv, row]; rfl)

theorem emitted_refElem {le : LEnv} {before : LS} {view index : ValueId} {mu : Mutability}
    {element : Ty} {intType : IntTy}
    (viewTyped : before.vals[view]? = some (some (.view mu element)))
    (indexTyped : before.vals[index]? = some (some (.data (.int intType)))) :
    EmittedAt le before (emitDef (.refElem view index)) := by
  exact .emit .refl _ (.data (.ref mu element)) (by
    simp [Op.resultTy, TyEnv.viewTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
      viewTyped, indexTyped, pure, Except.pure, bind, Except.bind])

theorem emitted_snapshot {le : LEnv} {before : LS} {value : ValueId} {mu : Mutability} {owner element : Ty}
    (typed : before.vals[value]? = some (some (.data (.ref mu owner))))
    (array : arrayElem? owner = some element) (mode : GIR.SnapshotMode) :
    EmittedAt le before (emitDef (.snapshot mode value)) := by
  apply EmittedTrace.emit .refl _
    (.view (if ((tyEnv le before).contentsWritable value).getD (mode == .owner || mu == .mutable)
      then .mutable else .readOnly) element)
  simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, typed, array,
    pure, Except.pure, bind, Except.bind]

end Goose.Lower.Validation
