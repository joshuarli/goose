import Goose.Lower.Validation.SnapshotContentsControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def SnapshotContentsRetention (le : LEnv) (first snapshot owner : ValueId)
    (before after : LS) : Prop :=
  ∀ authorized, SnapshotContentsWitness le first snapshot owner authorized before →
    SnapshotContentsWitness le first snapshot owner authorized after

theorem SnapshotContentsRetention.refl (le : LEnv) (first snapshot owner : ValueId) (state : LS) :
    SnapshotContentsRetention le first snapshot owner state state := fun _ witness => witness

theorem SnapshotContentsRetention.trans {le : LEnv} {first snapshot owner : ValueId}
    {before middle after : LS}
    (prior : SnapshotContentsRetention le first snapshot owner before middle)
    (suffix : SnapshotContentsRetention le first snapshot owner middle after) :
    SnapshotContentsRetention le first snapshot owner before after :=
  fun authorized witness => suffix authorized (prior authorized witness)

theorem snapshotContentsRetention_of_framed_run {α : Type} {action : B α} {le : LEnv}
    {first snapshot owner : ValueId} {before after : LS} {result : α} {loop : Option LoopCtx}
    (run : action le before = (result, after))
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (frameRun : GeneratedTargetFrameRun loop action)
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before) :
    SnapshotContentsRetention le first snapshot owner before after :=
  fun _ witness => witness.of_framed_run run dense advances typed frameRun generated frames

structure SnapshotSourceSite (le : LEnv) (snapshot : ValueId) (mode : SnapshotMode) (owner : ValueId) where
  typingEnv : TEnv
  results : List Ty
  place : Place
  info : PlaceInfo
  start : Nat
  finish : Nat
  beforePlace : LS
  ownerState : LS
  emittedState : LS
  aligned : le = lowerEnv typingEnv.mod typingEnv.vars results
  typed : tyPlace typingEnv place start = .ok (info, finish)
  generated : GeneratedBuilderState beforePlace
  lowered : lowerPlace place le beforePlace = (owner, ownerState)
  live : ownerState.cur.isSome = true
  emitted : emitDef (.snapshot mode owner) le ownerState = (snapshot, emittedState)

def SnapshotSourceTrace (le : LEnv) (first : ValueId) (captured current : LS) : Prop :=
  ∀ snapshot mode owner, .def snapshot (.snapshot mode owner) ∈ captured.insts → first ≤ snapshot →
    ∃ site : SnapshotSourceSite le snapshot mode owner,
      first ≤ site.beforePlace.vals.size ∧ site.emittedState.Ext current ∧ TypePrefix site.emittedState current ∧
      SnapshotContentsRetention le site.beforePlace.vals.size snapshot owner site.emittedState current

theorem SnapshotSourceTrace.extend_framed {α : Type} {action : B α} {le : LEnv}
    {first : ValueId} {captured before after : LS} {result : α} {loop : Option LoopCtx}
    (trace : SnapshotSourceTrace le first captured before)
    (run : action le before = (result, after))
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (frameRun : GeneratedTargetFrameRun loop action)
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before) :
    SnapshotSourceTrace le first captured after := by
  intro snapshot mode owner member bounded
  obtain ⟨site, fresh, extension, prefixTypes, prior⟩ := trace snapshot mode owner member bounded
  exact ⟨site, fresh, extension.trans (advances le before result after run).ext,
    prefixTypes.trans (typed le before result after run),
    prior.trans (snapshotContentsRetention_of_framed_run run dense advances typed frameRun generated frames)⟩

private theorem snapshot_definition_blocks {le : LEnv} {state : LS} {snapshot owner : ValueId}
    {mode : SnapshotMode} (member : .def snapshot (.snapshot mode owner) ∈ state.insts) :
    ∃ block, block ∈ (permissionFunc le state).blocks.toList ∧
      .def snapshot (.snapshot mode owner) ∈ block.insts := by
  apply List.mem_flatMap.mp
  simpa only [permissionFunc, LS.insts, Array.toList_map, List.flatMap_map] using member

theorem SnapshotSourceTrace.empty (le : LEnv) (state : LS) (checked : state.DenseDefinitions) :
    SnapshotSourceTrace le state.vals.size state state := by
  intro snapshot mode owner member bound
  obtain ⟨block, belongs, defined⟩ := snapshot_definition_blocks (le := le) member
  exact (Nat.not_lt_of_ge bound (permissionFunc_def_bound checked belongs defined)).elim

theorem SnapshotSourceTrace.seq {le : LEnv} {first : ValueId} {middle after : LS}
    (prior : SnapshotSourceTrace le first middle after)
    (suffix : SnapshotSourceTrace le middle.vals.size after after)
    (firstBound : first ≤ middle.vals.size)
    (middleDense : middle.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : middle.Ext after) : SnapshotSourceTrace le first after after := by
  intro snapshot mode owner member bound
  by_cases old : snapshot < middle.vals.size
  · obtain ⟨block, belongs, defined⟩ := snapshot_definition_blocks (le := le) member
    obtain ⟨priorBlock, priorMember, priorDefined⟩ :=
      permissionFunc_old_definition middleDense afterDense extension belongs defined old
    have priorFlat : .def snapshot (.snapshot mode owner) ∈
        (permissionFunc le middle).blocks.toList.flatMap (·.insts) :=
      List.mem_flatMap.mpr ⟨priorBlock, priorMember, priorDefined⟩
    have priorInstructions : .def snapshot (.snapshot mode owner) ∈ middle.insts := by
      simpa only [permissionFunc, LS.insts, Array.toList_map, List.flatMap_map] using priorFlat
    exact prior snapshot mode owner priorInstructions bound
  · obtain ⟨site, fresh, extended, types, retained⟩ := suffix snapshot mode owner member (Nat.le_of_not_gt old)
    exact ⟨site, Nat.le_trans firstBound fresh, extended, types, retained⟩

end Goose.Lower.Validation
