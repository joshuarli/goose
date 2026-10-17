import Goose.Lower.Validation.EmittedTypingOperations
import Goose.Lower.Validation.BuilderTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem EmittedAt.recordReadValueRootRecipe (le : LEnv) (before : LS)
    (value : ValueId) (place : Place) :
    EmittedAt le before (Goose.Lower.recordReadValueRootRecipe value place) := by
  have values : (Goose.Lower.recordReadValueRootRecipe value place le before).2.vals = before.vals := by
    cases place <;> simp only [recordReadValueRootRecipe_run] <;> first
      | rfl
      | (split <;> simp only [recordValueRootSource_run] <;> rfl)
  have blocks : (Goose.Lower.recordReadValueRootRecipe value place le before).2.blocks = before.blocks := by
    cases place <;> simp only [recordReadValueRootRecipe_run] <;> first
      | rfl
      | (split <;> simp only [recordValueRootSource_run] <;> rfl)
  apply EmittedAt.of_preserving _ (EmittedTypePrefix.of_vals values)
  intro result op member
  simpa only [LS.insts, blocks] using member

theorem emitted_lowerPlace_var {env : Core.TEnv} {variableId : VarId} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env (.var variableId) start = .ok (info, finish))
    (results : List Ty) (before : LS) :
    EmittedAt (lowerEnv env.mod env.vars results) before (lowerPlace (.var variableId)) := by
  simp only [Core.tyPlace] at source
  obtain ⟨localVar, next, lookup, shape⟩ := (st_bind_ok _ _ _ _).mp source
  have row := (varOf_ok _ _ _ _).mp lookup
  have slotRow : (lowerEnv env.mod env.vars results).slots[variableId]? =
      some ⟨localVar.ty, localVar.kind, localVar.scope, variableId⟩ := by
    simp [lowerEnv, Array.getElem?_mapIdx, row.2.1]
  exact emitted_slotAddr slotRow

theorem emitted_lowerPlace_global {env : Core.TEnv} {globalId : GlobalId} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env (.global globalId) start = .ok (info, finish))
    (results : List Ty) (before : LS) :
    EmittedAt (lowerEnv env.mod env.vars results) before (lowerPlace (.global globalId)) := by
  by_cases available : globalId < env.globalLimit
  · cases row : env.mod.globals[globalId]? with
    | none => simp [Core.tyPlace, available, row, chk] at source
    | some global =>
      have globalRow : (lowerEnv env.mod env.vars results).globals[globalId]? = some (global.ty, global.kind) := by
        simp [lowerEnv, Array.getElem?_map, row]
      exact emitted_globalAddr globalRow
  · simp [Core.tyPlace, available, chk] at source

theorem emitted_lowerExpr_ref {le : LEnv} {before : LS} (requested : Mutability) (place : Place)
    (child : EmittedAt le before (lowerPlace place)) :
    EmittedAt le before (lowerExpr (.ref requested place)) := by
  exact child.bind (emitted_borrowTo le _ requested _)

theorem emitted_lowerArg_byRef {le : LEnv} {before : LS} (requested : Mutability) (place : Place)
    (child : EmittedAt le before (lowerPlace place)) :
    EmittedAt le before (lowerArg (.byRef requested place)) := by
  exact child.bind (emitted_borrowTo le _ requested _)

theorem emitted_lowerExpr_read {le : LEnv} {before : LS} (place : Place)
    (child : EmittedAt le before (lowerPlace place))
    (typed : ∀ block, (lowerPlace place le before).2.cur = some block →
      ∃ mu type, (lowerPlace place le before).2.vals[(lowerPlace place le before).1]? =
        some (some (.data (.ref mu type)))) :
    EmittedAt le before (lowerExpr (.read place)) := by
  apply child.bind
  apply EmittedAt.bind
  · apply EmittedAt.emitDef
    intro live
    cases current : (lowerPlace place le before).2.cur with
    | none => simp [current] at live
    | some block =>
      obtain ⟨mu, type, recorded⟩ := typed block current
      exact ⟨.data type, by
        simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, recorded,
          pure, Except.pure, bind, Except.bind]⟩
  · apply (EmittedAt.recordReadValueRootRecipe le _ _ place).bind
    exact EmittedAt.pure le _ _

theorem emitted_lowerExpr_read_var {env : Core.TEnv} {variableId : VarId} {type : Ty}
    {start finish : Nat} (source : Core.tyExpr env (.read (.var variableId)) start = .ok (type, finish))
    (results : List Ty) (before : LS) :
    EmittedAt (lowerEnv env.mod env.vars results) before (lowerExpr (.read (.var variableId))) := by
  obtain ⟨info, next, placeSource, same⟩ := tyExpr_read_place source
  apply emitted_lowerExpr_read (.var variableId) (emitted_lowerPlace_var placeSource results before)
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

theorem emitted_lowerExpr_read_global {env : Core.TEnv} {globalId : GlobalId} {type : Ty}
    {start finish : Nat} (source : Core.tyExpr env (.read (.global globalId)) start = .ok (type, finish))
    (results : List Ty) (before : LS) :
    EmittedAt (lowerEnv env.mod env.vars results) before (lowerExpr (.read (.global globalId))) := by
  obtain ⟨info, next, placeSource, same⟩ := tyExpr_read_place source
  apply emitted_lowerExpr_read (.global globalId) (emitted_lowerPlace_global placeSource results before)
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
