import Goose.Lower.Validation.SnapshotContentsSourceControlExpressions
import Goose.Lower.Validation.SourceStatementTypingControl
import Goose.Lower.Validation.SourceStatementTypingTransfers

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem SnapshotTraceRun.ifThen {le : LEnv} {loop : Option LoopCtx}
    (condition : ValueId) {body : B ValueId} (bodySource : SnapshotSourceAction le loop body) :
    SnapshotTraceRun le loop (Goose.Lower.whenLive () fun _ => do
      let (target, join) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some target)
      let _ ← body
      Goose.Lower.emitTerm (.br join [])
      Goose.Lower.setCur (some join)) := by
  have checked := snapshot_control_selected
    ((SnapshotSourceAction.fork le loop condition).bind fun pair => SnapshotSourceAction.pure le loop (pair.1, pair.2, ()))
    ((SnapshotFreeRun.fork condition).bind fun pair => SnapshotFreeRun.pure (pair.1, pair.2, ())) bodySource
    (arguments := fun _ => []) (by
      intro before output after generated run
      obtain ⟨pair, forked, forkRun, done⟩ := bind_eq.mp run
      obtain ⟨rfl, rfl⟩ := pure_eq.mp done
      have ids := fork_ids forkRun
      refine ⟨?_, ?_, ?_⟩
      · have id := congrArg Prod.fst ids.1
        have size := ids.2
        nat_omega
      · have id := congrArg Prod.snd ids.1
        have size := ids.2
        nat_omega
      · obtain ⟨block, row, params⟩ := (fork_emptyRows forkRun).2
        exact ⟨block, row, by intro param member; rw [params] at member; cases member⟩)
  intro before result after generated frames run
  cases live : before.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact .empty le before generated.dense
  | some current =>
    rw [whenLive_some _ _ _ live] at run
    apply checked before result after generated frames
    simpa only [bind_run, pure_run] using run

theorem SnapshotSourceAction.ifThen {le : LEnv} {loop : Option LoopCtx}
    (condition : ValueId) {body : B ValueId} (child : SnapshotSourceAction le loop body) :
    SnapshotSourceAction le loop (Goose.Lower.whenLive () fun _ => do
      let (target, join) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some target)
      let _ ← body
      Goose.Lower.emitTerm (.br join [])
      Goose.Lower.setCur (some join)) :=
  ⟨SnapshotTraceRun.ifThen condition child, dense_ifS_none_core condition child.dense,
    advB_ifS_none_core condition child.advance,
    generatedTargets_ifS_none_core loop condition child.targets child.advance,
    types_ifS_none_core condition child.types,
    generatedTargetFrame_ifS_none_core loop condition
      (GeneratedTargetFrameRun.bind child.frames (fun _ => generatedTargetFrame_pure loop ()))⟩

theorem SnapshotSourceAction.ifArms {le : LEnv} {loop : Option LoopCtx}
    (condition : ValueId) {yes no : B ValueId}
    (yesSource : SnapshotSourceAction le loop yes) (noSource : SnapshotSourceAction le loop no) :
    SnapshotSourceAction le loop (Goose.Lower.whenLive () fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← yes
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← no
      let endF ← Goose.Lower.curBlock
      Goose.Lower.joinArms endT endF) :=
  ⟨SnapshotTraceRun.ifArms condition yesSource noSource,
    dense_ifS_some_core condition yesSource.dense noSource.dense,
    advB_ifS_some_core condition yesSource.advance noSource.advance,
    generatedTargets_ifS_some_core loop condition yesSource.targets noSource.targets,
    types_ifS_some_core condition yesSource.types noSource.types,
    generatedTargetFrame_ifS_some_core loop condition yesSource.frames noSource.frames⟩

theorem snapshot_source_conditional {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (condition : Expr) (yes : Core.Block) (otherwise : Option Core.Block) (origin : OriginId)
    (conditionChild : SnapshotSourceExpression env results condition)
    (yesChild : ∀ env, SnapshotSourceBlock env results yes)
    (otherwiseChild : ∀ body, otherwise = some body → ∀ env, SnapshotSourceBlock env results body) :
    SnapshotSourceStatement env results scope (.ifS condition yes otherwise origin) := by
  intro output start finish source loop
  obtain ⟨conditionFinish, yesType, yesFinish, conditionSource, yesSource, otherwiseSource, _⟩ := tyStmt_if_children source
  cases otherwise with
  | none =>
    exact (((SnapshotSourceAction.lowerExpr condition (conditionChild conditionSource)).withLoop loop).bind fun value =>
      SnapshotSourceAction.ifThen value
        (SnapshotSourceAction.lowerBlock loop [] false yes (yesChild env yesSource loop [] false))).snapshots
  | some no =>
    obtain ⟨noType, noSource⟩ := otherwiseSource
    exact (((SnapshotSourceAction.lowerExpr condition (conditionChild conditionSource)).withLoop loop).bind fun value =>
      SnapshotSourceAction.ifArms value
        (SnapshotSourceAction.lowerBlock loop [] false yes (yesChild env yesSource loop [] false))
        (SnapshotSourceAction.lowerBlock loop [] false no (otherwiseChild no rfl env noSource loop [] false))).snapshots

theorem SnapshotFreeRun.curBlock : SnapshotFreeRun Goose.Lower.curBlock := fun _ _ => .refl _

theorem SnapshotFreeRun.whenLive (default : α) {body : BlockId → B α}
    (child : ∀ block, SnapshotFreeRun (body block)) : SnapshotFreeRun (Goose.Lower.whenLive default body) := by
  unfold Goose.Lower.whenLive
  refine SnapshotFreeRun.curBlock.bind fun current => ?_
  cases current with
  | none => exact SnapshotFreeRun.pure default
  | some block => exact child block

theorem snapshot_source_assert {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (condition : Expr) (origin : OriginId) (child : SnapshotSourceExpression env results condition) :
    SnapshotSourceStatement env results scope (.assertS condition origin) := by
  intro output start finish source loop
  have conditionSource := (tyStmt_assert_children source).1
  refine (((SnapshotSourceAction.lowerExpr condition (child conditionSource)).withLoop loop).bind fun value => ?_).snapshots
  refine ⟨SnapshotTraceRun.of_free ?_, dense_assert_core value origin, advB_assert_core value origin,
    generatedTargets_assert_core loop value origin, types_assert_core value origin,
    generatedTargetFrame_assert_core loop value origin⟩
  apply SnapshotFreeRun.whenLive
  intro current
  exact (SnapshotFreeRun.fork value).bind fun pair => (SnapshotFreeRun.setCur _).bind fun _ =>
    (SnapshotFreeRun.emitTerm _).bind fun _ => SnapshotFreeRun.setCur _

end Goose.Lower.Validation
