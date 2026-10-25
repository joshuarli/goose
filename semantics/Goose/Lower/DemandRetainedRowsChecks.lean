import Goose.Lower.DemandRetainedRows
import Goose.Lower.LifetimeChecks

namespace Goose.Lower.DemandRetainedRowsChecks

open Goose.Core Goose.GIR Goose.Core.Sound

private def implementation : Impl :=
  { name := "main", params := #[], results := #[], vars := #[],
    body := .mk 0 [] none, summary := .unknown }

private def sourceModule : Core.Module :=
  { files := #["retained.goose"], types := #[],
    globals := #[⟨"owner", .limited (.int .i64) 1, .mutable,
      .arrLit (.limited (.int .i64) 1) [.lit .i64 9], 0⟩],
    impls := #[implementation],
    contexts := #[⟨0, "main", [], [], []⟩], entry := 0, origins := #[⟨0, 1, "owner"⟩], profile := .shrink }

private def before : LS := { initState with blocks := #[⟨[], #[]⟩], cur := some 0 }
private def lowered : ValueId × LS := lowerView (.of (.global 0)) (lowerEnv sourceModule #[] []) before
private def snapshotId : ValueId := lowered.1
private def loweredClear : Unit × LS :=
  emitEffect (.clear 0 (some 0)) (lowerEnv sourceModule #[] []) lowered.2
private def function : Func :=
  { name := "sample", params := [], results := [], slots := #[], scopes := #[],
    blocks := finishBlocks loweredClear.2.blocks, summary := .unknown, org := none }
private def context : FnCtx := ⟨⟨.release, lower sourceModule⟩, function⟩
private def addressFrame : Frame := (⟨0, [], {}, 0⟩ : Frame).set 0 (.val (.ref ⟨.global 0, []⟩))
private def sampledFrame : Frame := addressFrame.set snapshotId (.view LifetimeChecks.sampledView)
private def fullOwner : St :=
  ⟨Store.empty.introduce (.global 0) (.limited (.int .i64) 1 LifetimeChecks.physicalSlots 1), "", 0, 0⟩
private def cleared : St :=
  { fullOwner with store := ⟨(fullOwner.store.roots.erase (.global 0)).insert (.global 0)
    (.limited (.int .i64) 1 LifetimeChecks.physicalSlots 0)⟩ }
private def sliceAlias : RetainedAlias := ⟨.slice .readOnly (.int .i64), [.global 0], .operand [0]⟩
private def required : RetainedSsaMap := (⟨[], []⟩ : RetainedSsaMap).withRun snapshotId sliceAlias

theorem actual_generated_snapshot :
    DemandInstructionStep context 0 ⟨(0, 1), addressFrame, fullOwner⟩
      ⟨(0, 2), sampledFrame, fullOwner⟩ := by
  apply DemandInstructionStep.definition (id := snapshotId) (op := .snapshot .owner 0) (by cbv)
  simp [execOp, execPure, addressFrame, Frame.set, getVal, getCell, fullOwner, Store.introduce,
    Store.empty, Store.read, Val.get?, readLoc, expectRef, expectArray, LifetimeChecks.physicalSlots,
    LifetimeChecks.sampledView, bind_apply, pure_apply]

theorem actual_limited_clear :
    DemandInstructionStep context 0 ⟨(0, 2), sampledFrame, fullOwner⟩
      ⟨(0, 3), sampledFrame, cleared⟩ := by
  apply DemandInstructionStep.effect (effect := .clear 0 (some 0)) (by cbv)
  cbv

theorem source_view_alias :
    (⟨sourceModule, initImpl, initContext, []⟩ : PEnv).access.aliasView [0] (.of (.global 0)) =
      .ok [sliceAlias] := by cbv

private theorem physical_slice (m : Core.Module) (world : World) (env : Env) :
    SliceRunAliasAt m world env cleared.store sampledFrame snapshotId sliceAlias := by
  obtain ⟨view, mutability, element, capacity, cell, type, alias, physical⟩ :=
    LifetimeChecks.retained_limited_sample m world env
  have expectedCell : LifetimeChecks.sampledFrame.vals[0]? = some (.view LifetimeChecks.sampledView) :=
    Frame.set_get _ _ _
  have same : view = LifetimeChecks.sampledView := RVal.view.inj (Option.some.inj (cell.symm.trans expectedCell))
  subst view
  change Ty.ref .mutable (.limited (.int .i64) 1) = Ty.ref mutability (.limited element capacity) at type
  cases type
  refine ⟨LifetimeChecks.sampledView, .readOnly, .int .i64, Frame.set_get _ _ _, rfl, ?_⟩
  constructor
  · have growth : Goose.Proofs.Memory.StoreLe LifetimeChecks.clearedOwner cleared.store := by
      intro root value row
      refine ⟨value, ?_, Goose.Proofs.Memory.Refines.refl value⟩
      have same : cleared.store.roots[root]? = LifetimeChecks.clearedOwner.roots[root]? := by
        by_cases equal : root = .global 0 <;>
          simp [cleared, fullOwner, LifetimeChecks.clearedOwner, Store.introduce, Store.empty,
            Std.HashMap.getElem?_insert, equal]
      rw [same]
      exact row
    exact ⟨LifetimeChecks.sampledView.loc, 0, 1, rfl, rfl, physical.mono growth⟩
  · intro root target
    change LifetimeChecks.sampledView.loc.root = root at target
    exact ⟨.global 0, by simp [sliceAlias], target.symm⟩

theorem generated_run_survives_limited_clear (m : Core.Module) (world : World) (env : Env) :
    required.Realizes m world env ⟨(0, 3), sampledFrame, cleared⟩ := by
  apply RetainedSsaMap.withRun_realizes
  · constructor <;> simp
  · exact Or.inl (physical_slice m world env)

theorem empty_map_cannot_cover_generated_run : ¬ (⟨[], []⟩ : RetainedSsaMap).Covers required := by
  intro coverage
  have member := coverage.2 (snapshotId, sliceAlias) (by simp [required, RetainedSsaMap.withRun])
  cases member

theorem different_ssa_row_cannot_cover_generated_run :
    ¬ ((⟨[], []⟩ : RetainedSsaMap).withRun (snapshotId + 1) sliceAlias).Covers required := by
  intro coverage
  have member := coverage.2 (snapshotId, sliceAlias) (by simp [required, RetainedSsaMap.withRun])
  simp [RetainedSsaMap.withRun] at member

theorem covered_generated_run_rejects_removed_backing (m : Core.Module) (world : World) (env : Env)
    (map : RetainedSsaMap) (coverage : map.Covers required) :
    ¬ map.Realizes m world env ⟨(0, 2), sampledFrame, LifetimeChecks.removedSample⟩ := by
  intro realized
  have sampled := (coverage.realizes realized).2 (snapshotId, sliceAlias)
    (by simp [required, RetainedSsaMap.withRun])
  obtain ⟨values, read⟩ := sampled.read_safe
  have expectedCell : sampledFrame.vals[snapshotId]? = some (.view LifetimeChecks.sampledView) := Frame.set_get _ _ _
  have originalCell : LifetimeChecks.sampledFrame.vals[0]? = some (.view LifetimeChecks.sampledView) := Frame.set_get _ _ _
  have failed : (getView sampledFrame snapshotId >>= readRun) LifetimeChecks.removedSample =
      .stop (.fault .pathRange) LifetimeChecks.removedSample := by
    simpa only [getView_of expectedCell, getView_of originalCell] using LifetimeChecks.removed_sample_faults
  rw [failed] at read
  cases read

end Goose.Lower.DemandRetainedRowsChecks
