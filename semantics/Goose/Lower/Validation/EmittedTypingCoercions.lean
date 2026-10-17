import Goose.Lower.Validation.EmittedTypingPlaceCheckpoints

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem EmittedBuilder.coerceTo {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (target : Ty) (value : ValueId) (origin : OriginId) :
    EmittedBuilder le initial (Goose.Lower.coerceTo target value origin le before).2 := by
  have sameState : (Goose.Lower.coerceTo target value origin le before).2 =
      match target, (Goose.Lower.valTy value le before).1 with
      | .ref .readOnly _, .data (.ref .mutable _) => (Goose.Lower.emitDef (.refFreeze value) le before).2
      | .slice .readOnly _, .data (.slice .mutable _) =>
        let view := Goose.Lower.emitDef (.sliceView value) le before
        (Goose.Lower.emitDef (.viewSlice .readOnly view.1 .omitted .omitted (some origin)) le view.2).2
      | _, _ => before := by
    simp only [Goose.Lower.coerceTo, bind_run, valTy_run]
    split <;> simp_all only [bind_run, pure_run]
  rw [sameState]
  split
  next targetElement sourceElement observed =>
    have row := emitted_valTy_nonunit (by intro h; cases h) observed
    apply builder.emitDef (.refFreeze value)
    · intro active
      exact ⟨.data (.ref .readOnly sourceElement), by
        simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, row,
          pure, Except.pure, bind, Except.bind]⟩
    · intro active operand member
      have same : operand = value := by simpa [Op.uses] using member
      subst operand
      exact (Array.getElem?_eq_some_iff.mp row).1
  next targetElement sourceElement observed =>
    have row := emitted_valTy_nonunit (by intro h; cases h) observed
    let view := Goose.Lower.emitDef (.sliceView value) le before
    have success : (Op.sliceView value).resultTy (tyEnv le before) = .ok (.view .mutable sourceElement) := by
      simp [Op.resultTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, row, pure, Except.pure, bind, Except.bind]
    have viewed := builder.emitDef (.sliceView value) (fun _ => ⟨.view .mutable sourceElement, success⟩) (by
      intro active operand member
      have same : operand = value := by simpa [Op.uses] using member
      subst operand
      exact (Array.getElem?_eq_some_iff.mp row).1)
    have recorded : view.2.cur.isSome = true → view.2.vals[view.1]? = some (some (.view .mutable sourceElement)) := by
      intro active
      cases current : before.cur with
      | none =>
        have stopped := emitDef_none (.sliceView value) le current
        have dead : view.2 = before := congrArg Prod.snd stopped
        rw [dead, current] at active
        cases active
      | some block => exact (emitDef_recorded current success).2.2.1
    apply viewed.emitDef (.viewSlice .readOnly view.1 .omitted .omitted (some origin))
    · intro active
      have typed := recorded active
      dsimp only [view] at typed
      exact ⟨.data (.slice .readOnly sourceElement), by
        simp [view, Op.resultTy, TyEnv.viewTy, TyEnv.valTy, TyEnv.boundTy, tyEnv, typed,
          Mutability.atLeast, pure, Except.pure, bind, Except.bind]⟩
    · intro active operand member
      have same : operand = view.1 := by simpa [Op.uses, Bnd.uses] using member
      subst operand
      exact (Array.getElem?_eq_some_iff.mp (recorded active)).1
  next => exact builder

theorem EmittedBuilder.coerceSlot {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (slot : SlotId) (value : ValueId) (origin : OriginId) :
    EmittedBuilder le initial (Goose.Lower.coerceSlot slot value origin le before).2 := by
  cases row : le.slots[slot]? with
  | none => simpa only [Goose.Lower.coerceSlot, bind_run, read_apply, row, pure_run] using builder
  | some descriptor =>
    simpa only [Goose.Lower.coerceSlot, bind_run, read_apply, row] using builder.coerceTo descriptor.ty value origin

theorem EmittedBuilder.coerceResult {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (value : ValueId) (origin : OriginId) :
    EmittedBuilder le initial (Goose.Lower.coerceResult value origin le before).2 := by
  cases row : le.results.head? with
  | none => simpa only [Goose.Lower.coerceResult, bind_run, read_apply, row, pure_run] using builder
  | some type =>
    simpa only [Goose.Lower.coerceResult, bind_run, read_apply, row] using builder.coerceTo type value origin

end Goose.Lower.Validation
