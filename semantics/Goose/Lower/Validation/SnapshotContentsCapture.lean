import Goose.Lower.Validation.SnapshotContentsSource

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem snapshot_emit_instructions {le : LEnv} {before after : LS}
    {value : ValueId} {op : Op} {current : BlockId}
    (bounded : LiveBound before) (live : before.cur = some current)
    (run : emitDef op le before = (value, after)) :
    List.Perm after.insts (before.insts ++ [.def value op]) := by
  rw [emitDef_run op le live] at run
  obtain ⟨valueEq, stateEq⟩ := Prod.mk.inj run
  have emitted := LS.insts.modifyPush (bounded current live) (.def before.vals.size op)
  simpa only [← valueEq, ← stateEq, LS.insts] using emitted

theorem SnapshotSourceTrace.capture {le : LEnv} {first snapshot owner : ValueId}
    {mode : SnapshotMode} (site : SnapshotSourceSite le snapshot mode owner)
    (trace : SnapshotSourceTrace le first site.ownerState site.ownerState)
    (sourceFresh : first ≤ site.beforePlace.vals.size) :
    SnapshotSourceTrace le first site.emittedState site.emittedState := by
  have generated := site.generated.lowerPlace site.place site.lowered
  have carried := trace.extend_framed site.emitted (dense_emitDef _) (advB_emitDef _)
    (types_emitDef _) (generatedTargetFrame_emitDef none _) generated trivial
  cases live : site.ownerState.cur with
  | none =>
    have active := site.live
    simp [live] at active
  | some current =>
    have instructions := snapshot_emit_instructions generated.live live site.emitted
    intro value actualMode actualOwner member bound
    rcases List.mem_append.mp (instructions.mem_iff.mp member) with prior | added
    · exact carried value actualMode actualOwner prior bound
    · have equal := List.mem_singleton.mp added
      cases equal
      exact ⟨site, sourceFresh, .refl _, .refl _, .refl _ _ _ _ _⟩

theorem SnapshotSourceTrace.emitDef {le : LEnv} {first value : ValueId}
    {before after : LS} {op : Op}
    (trace : SnapshotSourceTrace le first before before)
    (generated : GeneratedBuilderState before)
    (run : Goose.Lower.emitDef op le before = (value, after))
    (notSnapshot : ∀ mode owner, op ≠ .snapshot mode owner) :
    SnapshotSourceTrace le first after after := by
  cases live : before.cur with
  | none =>
    rw [emitDef_none op le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact trace
  | some current =>
    have carried := trace.extend_framed run (dense_emitDef _) (advB_emitDef _)
      (types_emitDef _) (generatedTargetFrame_emitDef none _) generated trivial
    have instructions := snapshot_emit_instructions generated.live live run
    intro snapshot mode owner member bound
    rcases List.mem_append.mp (instructions.mem_iff.mp member) with prior | added
    · exact carried snapshot mode owner prior bound
    · have equal := List.mem_singleton.mp added
      exact (notSnapshot mode owner (Inst.def.inj equal).2.symm).elim

def NoNewSnapshots (before after : LS) : Prop :=
  ∀ snapshot mode owner, .def snapshot (.snapshot mode owner) ∈ after.insts →
    .def snapshot (.snapshot mode owner) ∈ before.insts

theorem SnapshotSourceTrace.recapture {le : LEnv} {first : ValueId} {captured after current : LS}
    (trace : SnapshotSourceTrace le first captured current)
    (unchanged : NoNewSnapshots captured after) : SnapshotSourceTrace le first after current := by
  intro snapshot mode owner member bound
  exact trace snapshot mode owner (unchanged snapshot mode owner member) bound

theorem NoNewSnapshots.refl (state : LS) : NoNewSnapshots state state := fun _ _ _ member => member

theorem NoNewSnapshots.trans {before middle after : LS}
    (first : NoNewSnapshots before middle) (second : NoNewSnapshots middle after) :
    NoNewSnapshots before after := fun snapshot mode owner member =>
  first snapshot mode owner (second snapshot mode owner member)

theorem NoNewSnapshots.of_same_values {before after : LS}
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (same : after.vals.size = before.vals.size) :
    NoNewSnapshots before after := by
  intro snapshot mode owner member
  have bound := snapshot_definition_lt afterDense member
  rw [same] at bound
  exact snapshot_instruction_before beforeDense afterDense extension bound member

theorem SnapshotSourceTrace.extend_same_values {α : Type} {action : B α} {le : LEnv}
    {first : ValueId} {before after : LS} {result : α} {loop : Option LoopCtx}
    (trace : SnapshotSourceTrace le first before before)
    (run : action le before = (result, after))
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (frameRun : GeneratedTargetFrameRun loop action)
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before)
    (same : after.vals.size = before.vals.size) :
    SnapshotSourceTrace le first after after := by
  apply (trace.extend_framed run dense advances typed frameRun generated frames).recapture
  exact NoNewSnapshots.of_same_values generated.dense
    (dense le before result after run generated.dense generated.live).1
    (advances le before result after run).ext same

end Goose.Lower.Validation
