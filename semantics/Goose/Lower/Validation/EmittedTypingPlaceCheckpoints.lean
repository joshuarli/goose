import Goose.Lower.Validation.EmittedTypingCheckpoints
import Goose.Lower.Validation.EmittedTypingPlaces

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem EmittedBuilder.freezeTo {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (requested : Mutability) (value : ValueId) :
    EmittedBuilder le initial (Goose.Lower.freezeTo requested value le before).2 := by
  have sameState : (Goose.Lower.freezeTo requested value le before).2 =
      match requested, (valTy value le before).1 with
      | .readOnly, .data (.ref .mutable _) => (Goose.Lower.emitDef (.refFreeze value) le before).2
      | _, _ => before := by
    simp only [Goose.Lower.freezeTo, bind_run, valTy_run]
    split <;> simp_all [pure_run]
  rw [sameState]
  split
  next element observed =>
    have row := emitted_valTy_nonunit (by intro h; cases h) observed
    apply builder.emitDef (.refFreeze value)
    · intro active
      exact ⟨.data (.ref .readOnly element), by
        simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, row,
          pure, Except.pure, bind, Except.bind]⟩
    · intro active operand member
      have same : operand = value := by simpa [Op.uses] using member
      subst operand
      exact (Array.getElem?_eq_some_iff.mp row).1
  next => exact builder

theorem emitted_checked_lowerPlace_var {env : Core.TEnv} {variableId : VarId} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env (.var variableId) start = .ok (info, finish))
    (results : List Ty) {initial before : LS}
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerPlace (.var variableId) (lowerEnv env.mod env.vars results) before).2 := by
  simp only [Core.tyPlace] at source
  obtain ⟨localVar, next, lookup, shape⟩ := (st_bind_ok _ _ _ _).mp source
  have row := (varOf_ok _ _ _ _).mp lookup
  have slotRow : (lowerEnv env.mod env.vars results).slots[variableId]? =
      some ⟨localVar.ty, localVar.kind, localVar.scope, variableId⟩ := by
    simp [lowerEnv, Array.getElem?_mapIdx, row.2.1]
  apply builder.emitDef (.slotAddr variableId)
  · intro active
    simp only [Op.resultTy, tyEnv, slotRow]
    exact ⟨_, rfl⟩
  · intro active operand member
    simp [Op.uses] at member

theorem emitted_checked_lowerPlace_global {env : Core.TEnv} {globalId : GlobalId} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env (.global globalId) start = .ok (info, finish))
    (results : List Ty) {initial before : LS}
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerPlace (.global globalId) (lowerEnv env.mod env.vars results) before).2 := by
  by_cases available : globalId < env.globalLimit
  · cases row : env.mod.globals[globalId]? with
    | none => simp [Core.tyPlace, available, row, chk] at source
    | some global =>
      have globalRow : (lowerEnv env.mod env.vars results).globals[globalId]? = some (global.ty, global.kind) := by
        simp [lowerEnv, Array.getElem?_map, row]
      apply builder.emitDef (.globalAddr globalId)
      · intro active
        simp only [Op.resultTy, tyEnv, globalRow]
        exact ⟨_, rfl⟩
      · intro active operand member
        simp [Op.uses] at member
  · simp [Core.tyPlace, available, chk] at source

theorem emitted_checked_lowerExpr_ref {le : LEnv} {initial before : LS}
    (requested : Mutability) (place : Place)
    (child : EmittedBuilder le initial (lowerPlace place le before).2) :
    EmittedBuilder le initial (lowerExpr (.ref requested place) le before).2 := by
  exact child.freezeTo requested (lowerPlace place le before).1

theorem emitted_checked_lowerArg_byRef {le : LEnv} {initial before : LS}
    (requested : Mutability) (place : Place)
    (child : EmittedBuilder le initial (lowerPlace place le before).2) :
    EmittedBuilder le initial (lowerArg (.byRef requested place) le before).2 := by
  exact child.freezeTo requested (lowerPlace place le before).1

theorem emitted_checked_lowerExpr_read {le : LEnv} {initial before : LS} (place : Place)
    (child : EmittedBuilder le initial (lowerPlace place le before).2)
    (typed : ∀ block, (lowerPlace place le before).2.cur = some block →
      ∃ mu type, (lowerPlace place le before).2.vals[(lowerPlace place le before).1]? =
        some (some (.data (.ref mu type)))) :
    EmittedBuilder le initial (lowerExpr (.read place) le before).2 := by
  apply child.emitDef (.load (lowerPlace place le before).1)
  · intro active
    cases current : (lowerPlace place le before).2.cur with
    | none => simp [current] at active
    | some block =>
      obtain ⟨mu, type, row⟩ := typed block current
      exact ⟨.data type, by
        simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, row,
          pure, Except.pure, bind, Except.bind]⟩
  · intro active operand member
    cases current : (lowerPlace place le before).2.cur with
    | none => simp [current] at active
    | some block =>
      obtain ⟨mu, type, row⟩ := typed block current
      have same : operand = (lowerPlace place le before).1 := by simpa [Op.uses] using member
      subst operand
      exact (Array.getElem?_eq_some_iff.mp row).1


theorem emitted_checked_lowerExpr_read_var {env : Core.TEnv} {variableId : VarId} {type : Ty}
    {start finish : Nat} (source : Core.tyExpr env (.read (.var variableId)) start = .ok (type, finish))
    (results : List Ty) {initial before : LS}
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerExpr (.read (.var variableId)) (lowerEnv env.mod env.vars results) before).2 := by
  obtain ⟨info, next, placeSource, same⟩ := tyExpr_read_place source
  apply emitted_checked_lowerExpr_read (.var variableId) (emitted_checked_lowerPlace_var placeSource results builder)
  intro block current
  cases live : before.cur with
  | none =>
    have stopped := emitDef_none (.slotAddr variableId) (lowerEnv env.mod env.vars results) live
    simp only [lowerPlace, stopped] at current
    rw [live] at current
    cases current
  | some previous =>
    have place := lowerPlace_var_exact placeSource results before live
    exact ⟨_, _, place.2⟩

theorem emitted_checked_lowerExpr_read_global {env : Core.TEnv} {globalId : GlobalId} {type : Ty}
    {start finish : Nat} (source : Core.tyExpr env (.read (.global globalId)) start = .ok (type, finish))
    (results : List Ty) {initial before : LS}
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerExpr (.read (.global globalId)) (lowerEnv env.mod env.vars results) before).2 := by
  obtain ⟨info, next, placeSource, same⟩ := tyExpr_read_place source
  apply emitted_checked_lowerExpr_read (.global globalId) (emitted_checked_lowerPlace_global placeSource results builder)
  intro block current
  cases live : before.cur with
  | none =>
    have stopped := emitDef_none (.globalAddr globalId) (lowerEnv env.mod env.vars results) live
    simp only [lowerPlace, stopped] at current
    rw [live] at current
    cases current
  | some previous =>
    have place := lowerPlace_global_exact placeSource env.vars results before live
    exact ⟨_, _, place.2⟩

end Goose.Lower.Validation
