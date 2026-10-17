import Goose.Lower.Validation.SnapshotContentsSourceControlActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem snapshot_control_branches {le : LEnv} {loop : Option LoopCtx}
    (condition : ValueId) {yes no : B ValueId}
    (yesSource : SnapshotSourceAction le loop yes) (noSource : SnapshotSourceAction le loop no)
    (tail : Option BlockId → ValueId → Option BlockId → ValueId → B α)
    (tailTrace : ∀ first before after result endT valueT endF valueF,
      SnapshotSourceTrace le first before before → GeneratedBuilderState before →
      LoopBuilderFrames loop before → tail endT valueT endF valueF le before = (result, after) →
      SnapshotSourceTrace le first after after) :
    SnapshotTraceRun le loop (do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← yes
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← no
      let endF ← Goose.Lower.curBlock
      tail endT valueT endF valueF) := by
  intro before result after generated frames run
  simp only [bind_eq] at run
  obtain ⟨⟨tb, eb⟩, forked, forkRun, u1, startedT, startTRun, valueT, evaluatedT, firstRun,
    endT, readT, curTRun, u2, startedF, startFRun, valueF, evaluatedF, secondRun,
    endF, readF, curFRun, tailRun⟩ := run
  rw [curBlock_run] at curTRun curFRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj curTRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj curFRun
  have ids := fork_ids forkRun
  have advance := advB_fork condition le before _ _ forkRun
  have forkGenerated := generated.fork condition forkRun
  have forkTrace := (SnapshotSourceAction.fork le loop condition).snapshots before _ _ generated frames forkRun
  have thenBound : ∀ block, some tb = some block → block < forked.blocks.size := by
    intro block same
    have sameId := congrArg Prod.fst ids.1
    have size := ids.2
    have eq := Option.some.inj same
    change tb = before.blocks.size at sameId
    nat_omega
  have thenGenerated := forkGenerated.setCur (some tb) thenBound startTRun
  have thenTrace := forkTrace.setCur_full startTRun
  have thenExt : forked.Ext startedT := by
    rw [setCur_run] at startTRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj startTRun
    exact .refl _
  have thenValues : startedT.vals.size = forked.vals.size := by
    rw [setCur_run] at startTRun
    exact congrArg (fun pair => pair.2.vals.size) startTRun.symm
  have thenFrames := frames.mono (advance.ext.trans thenExt)
  have firstTrace := yesSource.snapshots.continue yesSource.dense yesSource.advance yesSource.types
    yesSource.frames thenTrace thenGenerated thenFrames (by rw [thenValues]; exact advance.vals) firstRun
  have firstGenerated := thenGenerated.of_runs yesSource.dense yesSource.targets thenFrames.toTargets firstRun
  have firstAdvance := yesSource.advance le startedT _ _ firstRun
  have elseBound : ∀ block, some eb = some block → block < evaluatedT.blocks.size := by
    intro block same
    have sameId := congrArg Prod.snd ids.1
    have size := ids.2
    have eq := Option.some.inj same
    have grows := firstAdvance.ext.1
    have initial := thenExt.1
    change eb = before.blocks.size + 1 at sameId
    nat_omega
  have elseGenerated := firstGenerated.setCur (some eb) elseBound startFRun
  have elseTrace := firstTrace.setCur_full startFRun
  have elseExt : evaluatedT.Ext startedF := by
    rw [setCur_run] at startFRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj startFRun
    exact .refl _
  have elseValues : startedF.vals.size = evaluatedT.vals.size := by
    rw [setCur_run] at startFRun
    exact congrArg (fun pair => pair.2.vals.size) startFRun.symm
  have elseFrames := thenFrames.mono (firstAdvance.ext.trans elseExt)
  have secondTrace := noSource.snapshots.continue noSource.dense noSource.advance noSource.types
    noSource.frames elseTrace elseGenerated elseFrames (by
      rw [elseValues]
      exact Nat.le_trans (by rw [thenValues]; exact advance.vals) firstAdvance.vals) secondRun
  have secondGenerated := elseGenerated.of_runs noSource.dense noSource.targets elseFrames.toTargets secondRun
  have secondFrames := elseFrames.mono (noSource.advance le startedF _ _ secondRun).ext
  exact tailTrace _ _ _ _ _ _ _ _ secondTrace secondGenerated secondFrames tailRun

theorem SnapshotTraceRun.ifValue {le : LEnv} {loop : Option LoopCtx}
    (condition : ValueId) {yes no : B ValueId}
    (yesSource : SnapshotSourceAction le loop yes) (noSource : SnapshotSourceAction le loop no) :
    SnapshotTraceRun le loop (Goose.Lower.whenLive 0 fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← yes
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← no
      let endF ← Goose.Lower.curBlock
      Goose.Lower.joinValue endT valueT endF valueF) := by
  intro before result after generated frames run
  cases live : before.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact .empty le before generated.dense
  | some current =>
    rw [whenLive_some _ _ _ live] at run
    exact snapshot_control_branches condition yesSource noSource
      (fun endT valueT endF valueF => Goose.Lower.joinValue endT valueT endF valueF)
      (fun _ _ _ _ _ _ _ _ trace generated frames run => trace.joinValue generated frames run)
      before result after generated frames run

theorem SnapshotTraceRun.ifArms {le : LEnv} {loop : Option LoopCtx}
    (condition : ValueId) {yes no : B ValueId}
    (yesSource : SnapshotSourceAction le loop yes) (noSource : SnapshotSourceAction le loop no) :
    SnapshotTraceRun le loop (Goose.Lower.whenLive () fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← yes
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← no
      let endF ← Goose.Lower.curBlock
      Goose.Lower.joinArms endT endF) := by
  intro before result after generated frames run
  cases live : before.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact .empty le before generated.dense
  | some current =>
    rw [whenLive_some _ _ _ live] at run
    exact snapshot_control_branches condition yesSource noSource
      (fun endT _ endF _ => Goose.Lower.joinArms endT endF)
      (fun _ _ _ _ _ _ _ _ trace generated frames run => trace.joinArms generated frames run)
      before result after generated frames run

end Goose.Lower.Validation
