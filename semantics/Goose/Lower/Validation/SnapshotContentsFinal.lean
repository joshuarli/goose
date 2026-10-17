import Goose.Lower.Validation.SnapshotContentsTyping
import Goose.Lower.Validation.ActualContents
import Goose.Lower.Validation.ValueTypeReconstructionContents

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem SnapshotSourceSite.freshContents {le : LEnv} {snapshot owner : ValueId}
    {mode : SnapshotMode} {after : LS} {element : Ty}
    (site : SnapshotSourceSite le snapshot mode owner)
    (types : TypePrefix site.emittedState after)
    (recorded : after.vals[snapshot]? = some (some (.view .mutable element))) :
    FreshContentsEvidence le site.beforePlace.vals.size site.ownerState owner := by
  have run : lowerPlace site.place
      (lowerEnv site.typingEnv.mod site.typingEnv.vars site.results) site.beforePlace =
      (owner, site.ownerState) := by
    rw [← site.aligned]
    exact site.lowered
  have contents : (tyEnv (lowerEnv site.typingEnv.mod site.typingEnv.vars site.results)
      site.ownerState).contentsWritable owner = some true := by
    rw [← site.aligned]
    exact site.actualContents types recorded
  have evidence := lowerPlace_generated_actual_contents site.place site.typed run site.live contents site.generated
  rw [← site.aligned] at evidence
  exact evidence

theorem SnapshotSourceTrace.mutableSnapshotGraphs {le : LEnv} {state : LS}
    {module : GIR.Module} {func : Func}
    (trace : SnapshotSourceTrace le 0 state state)
    (slots : le.slots = func.slots) (blocks : func.blocks = finishBlocks state.blocks)
    (globals : module.globals.map (·.kind) = le.globals.map (·.2))
    (structs : module.structs = le.mod.structs) :
    MutableSnapshotGraphs module func state := by
  intro snapshot mode owner definition element expected
  have recorded : state.vals[snapshot]? = some (some (.view .mutable element)) := by
    cases row : state.vals[snapshot]? with
    | none => simp [emittedValueType, row] at expected
    | some entry =>
      cases entry with
      | none => simp [emittedValueType, row] at expected
      | some type =>
        simp only [emittedValueType, row, Option.getD_some] at expected
        exact expected ▸ rfl
  obtain ⟨site, _, _, types, retention⟩ := trace snapshot mode owner definition (Nat.zero_le _)
  have evidence := site.freshContents types recorded
  cases current : site.ownerState.cur with
  | none =>
    have live := site.live
    simp [current] at live
  | some block =>
    obtain ⟨authorized, witness⟩ := snapshotContentsWitness_emit evidence site.ownerGenerated current site.emitted
    have finalWitness := retention authorized witness
    refine ⟨authorized, ?_, finalWitness.ownerMember, finalWitness.beforeSnapshot⟩
    have closed := finalWitness.closed.replace_function slots
      (show (permissionFunc le state).blocks = func.blocks from blocks.symm)
    simpa only [globals, structs] using closed

end Goose.Lower.Validation
