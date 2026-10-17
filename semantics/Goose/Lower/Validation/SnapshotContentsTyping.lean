import Goose.Lower.Validation.SnapshotContentsSource
import Goose.Lower.Validation.ExpressionTypingGenerated
import Goose.Lower.Validation.ValueTypeReconstructionPermissionGraph

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem snapshot_emit_recorded {le : LEnv} {before after : LS}
    {snapshot owner : ValueId} {mode : SnapshotMode}
    (live : before.cur.isSome = true)
    (run : emitDef (.snapshot mode owner) le before = (snapshot, after)) :
    after.vals[snapshot]? = some (some
      (((Op.snapshot mode owner).resultTy (tyEnv le before)).toOption.getD (.data .unit))) := by
  cases current : before.cur with
  | none => simp [current] at live
  | some block =>
    rw [emitDef_run (.snapshot mode owner) le current] at run
    obtain ⟨valueEq, stateEq⟩ := Prod.mk.inj run
    rw [← valueEq, ← stateEq]
    simp

theorem SnapshotSourceSite.ownerGenerated {le : LEnv} {snapshot owner : ValueId} {mode : SnapshotMode}
    (site : SnapshotSourceSite le snapshot mode owner) : GeneratedBuilderState site.ownerState :=
  site.generated.lowerPlace site.place site.lowered

theorem SnapshotSourceSite.ownerBound {le : LEnv} {snapshot owner : ValueId} {mode : SnapshotMode}
    (site : SnapshotSourceSite le snapshot mode owner) : owner < site.ownerState.vals.size := by
  have run : lowerPlace site.place
      (lowerEnv site.typingEnv.mod site.typingEnv.vars site.results) site.beforePlace =
      (owner, site.ownerState) := by
    rw [← site.aligned]
    exact site.lowered
  obtain ⟨mu, recorded⟩ := lowerPlace_generated_typed site.place site.typed run site.live site.generated
  exact (Array.getElem?_eq_some_iff.mp recorded).1

theorem snapshot_contents_total {le : LEnv} {state : LS} {owner : ValueId}
    (checked : state.DenseDefinitions) (bound : owner < state.vals.size) :
    ∃ contents, (tyEnv le state).contentsWritable owner = some contents := by
  let caps := (permissionFunc le state).permissionsFromTables (le.globals.map (·.2)) le.mod.structs state.vals
  have size : caps.size = state.vals.size := by
    exact (permissionsFromTables_size _ _ _ _).trans (permissionFunc_numValues checked le)
  have inside : owner < caps.size := by rw [size]; exact bound
  refine ⟨(caps[owner]'inside).2, ?_⟩
  change (caps[owner]?).map (·.2) = some (caps[owner]'inside).2
  rw [Array.getElem?_eq_getElem inside]
  rfl

theorem snapshot_mutable_requires_contents {le : LEnv} {state : LS} {owner : ValueId}
    {mode : SnapshotMode} {element : Ty}
    (checked : state.DenseDefinitions) (bound : owner < state.vals.size)
    (typed : (Op.snapshot mode owner).resultTy (tyEnv le state) = .ok (.view .mutable element)) :
    (tyEnv le state).contentsWritable owner = some true := by
  obtain ⟨contents, row⟩ := snapshot_contents_total checked bound
  cases contents with
  | true => exact row
  | false =>
    simp only [Op.resultTy, row, Option.getD_some, Bool.false_eq_true, ite_false] at typed
    cases reference : (tyEnv le state).refTy owner with
    | error message => simp [reference, bind, Except.bind] at typed
    | ok pair =>
      simp only [reference, bind, Except.bind] at typed
      cases shape : arrayElem? pair.2 with
      | none => simp [shape, tyErr] at typed
      | some actual => simp [shape, pure, Except.pure] at typed

theorem SnapshotSourceSite.actualContents {le : LEnv} {snapshot owner : ValueId} {mode : SnapshotMode}
    {after : LS} {element : Ty} (site : SnapshotSourceSite le snapshot mode owner)
    (types : TypePrefix site.emittedState after)
    (recorded : after.vals[snapshot]? = some (some (.view .mutable element))) :
    (tyEnv le site.ownerState).contentsWritable owner = some true := by
  have emitted := snapshot_emit_recorded site.live site.emitted
  have retained := types snapshot _ emitted
  have shape := Option.some.inj (Option.some.inj (retained.symm.trans recorded))
  have typed : (Op.snapshot mode owner).resultTy (tyEnv le site.ownerState) = .ok (.view .mutable element) := by
    cases result : (Op.snapshot mode owner).resultTy (tyEnv le site.ownerState) with
    | error message => simp [result, Except.toOption] at shape
    | ok type =>
      simp only [result, Except.toOption, Option.getD_some] at shape
      exact congrArg Except.ok shape
  exact snapshot_mutable_requires_contents site.ownerGenerated.dense site.ownerBound typed

end Goose.Lower.Validation
