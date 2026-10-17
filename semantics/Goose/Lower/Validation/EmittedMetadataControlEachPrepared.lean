import Goose.Lower.Validation.EmittedMetadataControlEachTypes
import Goose.Lower.Validation.EmittedMetadataActions
import Goose.Lower.Validation.EmittedTypingEachSource

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem EmittedMetadataAction.eachSampled (le : LEnv) (loop : Option LoopCtx) (regrow : Bool) (view : ValueId) :
    EmittedMetadataAction le loop (Goose.Lower.eachSampled regrow view) := by
  cases regrow with
  | false => exact .emitDef le loop (.viewLen view)
  | true => exact .pure le loop 0

theorem EmittedMetadataAction.eachElemValue (le : LEnv) (loop : Option LoopCtx)
    (slot : SlotId) (byRef : Bool) (address : ValueId) :
    EmittedMetadataAction le loop (Goose.Lower.eachElemValue slot byRef address) := by
  cases byRef with
  | false => exact .emitDef le loop (.load address)
  | true =>
    unfold Goose.Lower.eachElemValue
    simp only [ite_true]
    apply (EmittedMetadataAction.read le loop).bind
    intro observed
    cases row : observed.vars[slot]? with
    | none => exact .pure le loop address
    | some localVar =>
      cases type : localVar.ty <;> simp only [type]
      all_goals first
        | exact .pure le loop address
        | exact .borrowTo le loop _ address

theorem metadata_each_prepared {le : LEnv} {before : LS}
    (metadata : EmittedMetadata le before) (generated : GeneratedBuilderState before)
    (owner : Option ValueId) (view : ValueId) {mu : Mutability} {element : Ty} {current : BlockId}
    (live : before.cur = some current) (viewTyped : before.vals[view]? = some (some (.view mu element))) :
    let regrow := (regrowOf owner le before).1
    let sampled := eachSampled regrow view le before
    let started := emitDef (.constInt .i64 0) le sampled.2
    EmittedMetadata le started.2 ∧ GeneratedBuilderState started.2 ∧ started.2.cur = some current ∧
      started.2.vals[started.1]? = some (some (.data (.int .i64))) ∧
      EmittedEachLengthTypes started.2 regrow owner sampled.1 := by
  have zeroSuccess : (Op.constInt .i64 0).resultTy (tyEnv le before) = .ok (.data (.int .i64)) := by
    simp [Op.resultTy, show IntTy.i64.inRange 0 = true from by decide, pure, Except.pure]
  cases regrowCase : (regrowOf owner le before).1
  · let sampled := emitDef (.viewLen view) le before
    have sampleSuccess : (Op.viewLen view).resultTy (tyEnv le before) = .ok (.data (.int .i64)) := by
      simp [Op.resultTy, TyEnv.viewTy, TyEnv.valTy, tyEnv, viewTyped, pure, Except.pure, bind, Except.bind]
    have sampledMetadata := metadata.emitDef (.viewLen view)
    have sampledGenerated : GeneratedBuilderState sampled.2 := generated.emitDef (.viewLen view) (env := le) rfl
    have sampledRecorded := emitDef_recorded live sampleSuccess
    have sampleLive : sampled.2.cur = some current := sampledRecorded.2.1.trans live
    have startedMetadata := sampledMetadata.emitDef (.constInt .i64 0)
    have startedGenerated : GeneratedBuilderState (emitDef (.constInt .i64 0) le sampled.2).2 :=
      sampledGenerated.emitDef (.constInt .i64 0) (env := le) rfl
    have startedRecorded := emitDef_recorded sampleLive
      (show (Op.constInt .i64 0).resultTy (tyEnv le sampled.2) = .ok (.data (.int .i64)) from by
        simp [Op.resultTy, show IntTy.i64.inRange 0 = true from by decide, pure, Except.pure])
    exact ⟨startedMetadata, startedGenerated, startedRecorded.2.1.trans sampleLive, startedRecorded.2.2.1,
      (types_emitDef (.constInt .i64 0) le sampled.2 _ _ rfl) _ _ sampledRecorded.2.2.1⟩
  · have startedMetadata := metadata.emitDef (.constInt .i64 0)
    have startedGenerated : GeneratedBuilderState (emitDef (.constInt .i64 0) le before).2 :=
      generated.emitDef (.constInt .i64 0) (env := le) rfl
    have startedRecorded := emitDef_recorded live zeroSuccess
    have ownerTyped : EmittedEachLengthTypes before true owner 0 := emitted_regrowOf_owner regrowCase
    exact ⟨startedMetadata, startedGenerated, startedRecorded.2.1.trans live, startedRecorded.2.2.1,
      ownerTyped.retained (types_emitDef (.constInt .i64 0) le before _ _ rfl)⟩

#print axioms metadata_each_prepared

end Goose.Lower.Validation
