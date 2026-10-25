import Goose.Lower.Validation.ReplacementContentFlowSourceReadyBuilder
import Goose.Lower.Validation.ValueTypes
import Goose.Lower.Validation.BuilderTyping

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model
open Goose.Core.Sound

theorem readable_not_refSlice {type : Ty} (readable : type.readable = true) :
    type.isRefSlice = false := by
  cases type <;> simp_all [Ty.readable, Ty.isRefSlice]
  rename_i target
  cases target <;> simp_all [Ty.refTarget]

theorem typedRead_recording {typingEnv : TEnv} {place : Place} {type : Ty} {start finish : Nat}
    (source : Core.tyExpr typingEnv (.read place) start = .ok (type, finish))
    (results : List Ty) (value : ValueId) (before : LS) :
    recordReadValueRootRecipe value place (lowerEnv typingEnv.mod typingEnv.vars results) before =
      ((), before) := by
  cases place with
  | var variableId =>
    simp only [Core.tyExpr] at source
    obtain ⟨info, next, checked, rest⟩ := (st_bind_ok _ _ _ _).mp source
    have readable : info.ty.readable = true := by
      by_cases available : info.ty.readable = true
      · exact available
      · simp [available, rej_ok] at rest
    simp only [Core.tyPlace] at checked
    obtain ⟨localVar, _, lookup, infoChecked⟩ := (st_bind_ok _ _ _ _).mp checked
    have row := (varOf_ok _ _ _ _).mp lookup |>.2.1
    have infoType : info.ty = localVar.ty :=
      congrArg (fun pair => pair.1.ty) ((st_pure_ok _ _ _).mp infoChecked)
    have notSlice : localVar.ty.isRefSlice = false := readable_not_refSlice (infoType ▸ readable)
    simp [recordReadValueRootRecipe_run, lowerEnv, row, notSlice]
  | _ => simp [recordReadValueRootRecipe_run]

theorem typedRead_run {typingEnv : TEnv} {place : Place} {type : Ty} {start finish : Nat}
    (source : Core.tyExpr typingEnv (.read place) start = .ok (type, finish))
    (results : List Ty) (before : LS) :
    lowerExpr (.read place) (lowerEnv typingEnv.mod typingEnv.vars results) before =
      let address := lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before
      Lower.emitDef (.load address.1) (lowerEnv typingEnv.mod typingEnv.vars results) address.2 := by
  rw [lowerExpr_read_run]
  simp only [typedRead_recording source]

theorem readRecording_preserves (value : ValueId) (place : Place) (env : LEnv) (before : LS) :
    let after := (recordReadValueRootRecipe value place env before).2
    after.blocks = before.blocks ∧ after.vals = before.vals ∧ after.cur = before.cur := by
  cases place <;>
    simp [recordReadValueRootRecipe_run, recordValueRootSource_run] <;>
    (try split) <;> simp

theorem readRecording_ready {state : State} {value : ValueId} {place : Place} {env : LEnv}
    {before middle : LS} (ready : EmitsOnly (ReadyOperands state) before middle ∧
      (middle.cur.isSome = true → flowAt state.values value ≠ .pending)) :
    let after := (recordReadValueRootRecipe value place env middle).2
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  have unchanged := readRecording_preserves value place env middle
  exact ⟨ready.1.trans (.of_blocks unchanged.1), by simpa only [unchanged.2.2] using ready.2⟩

theorem readRecording_definition (value : ValueId) (place : Place) (operation : Op)
    (env : LEnv) (before : LS) :
    let recorded := (recordReadValueRootRecipe value place env before).2
    let actual := Lower.emitDef operation env recorded
    let original := Lower.emitDef operation env before
    actual.1 = original.1 ∧ actual.2.blocks = original.2.blocks ∧
      actual.2.vals = original.2.vals ∧ actual.2.cur = original.2.cur := by
  dsimp only
  have same := readRecording_preserves value place env before
  have typing : tyEnv env (recordReadValueRootRecipe value place env before).2 = tyEnv env before := by
    simp only [tyEnv, same.1, same.2.1]
  cases current : before.cur with
  | none =>
    rw [emitDef_none operation env (same.2.2.trans current), emitDef_none operation env current]
    exact ⟨rfl, same.1, same.2.1, same.2.2⟩
  | some block =>
    rw [emitDef_run operation env (same.2.2.trans current), emitDef_run operation env current]
    simp only [same.1, same.2.1, same.2.2, typing]
    repeat' constructor

#print axioms readRecording_preserves
#print axioms readRecording_ready
#print axioms typedRead_recording
#print axioms typedRead_run

end Goose.Lower.Validation.ReplacementContentFlowSource
