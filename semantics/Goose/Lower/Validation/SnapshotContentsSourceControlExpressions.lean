import Goose.Lower.Validation.SnapshotContentsSourceControlSelected
import Goose.Lower.Validation.SnapshotContentsSourceControlBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem SnapshotSourceAction.shortCircuit {le : LEnv} {loop : Option LoopCtx}
    (isAnd : Bool) (condition : ValueId) {body : B ValueId}
    (child : SnapshotSourceAction le loop body) :
    SnapshotSourceAction le loop (Goose.Lower.shortCircuit isAnd condition body) :=
  ⟨SnapshotTraceRun.shortCircuit isAnd condition child,
    dense_shortCircuit isAnd condition child.dense,
    advB_shortCircuit isAnd condition child.advance,
    generatedTargets_shortCircuit loop isAnd condition child.targets child.advance,
    types_shortCircuit isAnd condition child.types,
    generatedTargetFrame_shortCircuit loop isAnd condition child.frames⟩

theorem SnapshotSourceAction.ifValue {le : LEnv} {loop : Option LoopCtx}
    (condition : ValueId) (sourceScope : ScopeId) {yes no : B ValueId}
    (yesSource : SnapshotSourceAction le loop yes) (noSource : SnapshotSourceAction le loop no) :
    SnapshotSourceAction le loop (Goose.Lower.whenLive 0 fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← yes
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← no
      let endF ← Goose.Lower.curBlock
      let value ← Goose.Lower.joinValue endT valueT endF valueF
      Goose.Lower.recordValueRootRecipe value sourceScope
      Pure.pure value) :=
  ⟨SnapshotTraceRun.ifValue condition sourceScope yesSource noSource,
    dense_ifE_core condition sourceScope yesSource.dense noSource.dense,
    advB_ifE_core condition sourceScope yesSource.advance noSource.advance,
    generatedTargets_ifE_recorded_core loop condition sourceScope yesSource.targets noSource.targets,
    types_ifE_core condition sourceScope yesSource.types noSource.types,
    generatedTargetFrame_ifE_recorded_core loop condition sourceScope yesSource.frames noSource.frames⟩

theorem snapshot_source_and {env : Core.TEnv} {results : List Ty} (left right : Expr)
    (leftChild : SnapshotSourceExpression env results left) (rightChild : SnapshotSourceExpression env results right) :
    SnapshotSourceExpression env results (.and left right) := by
  intro type start finish source
  obtain ⟨leftType, leftFinish, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, rightStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨rightType, rightFinish, rightSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact ((SnapshotSourceAction.lowerExpr left (leftChild leftSource)).bind fun value =>
    SnapshotSourceAction.shortCircuit true value (SnapshotSourceAction.lowerExpr right (rightChild rightSource))).snapshots

theorem snapshot_source_or {env : Core.TEnv} {results : List Ty} (left right : Expr)
    (leftChild : SnapshotSourceExpression env results left) (rightChild : SnapshotSourceExpression env results right) :
    SnapshotSourceExpression env results (.or left right) := by
  intro type start finish source
  obtain ⟨leftType, leftFinish, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, rightStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨rightType, rightFinish, rightSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact ((SnapshotSourceAction.lowerExpr left (leftChild leftSource)).bind fun value =>
    SnapshotSourceAction.shortCircuit false value (SnapshotSourceAction.lowerExpr right (rightChild rightSource))).snapshots

theorem snapshot_source_ifExpression {env : Core.TEnv} {results : List Ty}
    (condition : Expr) (yes no : Core.Block) (conditionChild : SnapshotSourceExpression env results condition)
    (yesChild : ∀ env, SnapshotSourceBlock env results yes) (noChild : ∀ env, SnapshotSourceBlock env results no) :
    SnapshotSourceExpression env results (.ifE condition yes no) := by
  intro type start finish source
  obtain ⟨conditionType, conditionFinish, conditionSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, yesStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨yesType, yesFinish, yesSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨noType, noFinish, noSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact ((SnapshotSourceAction.lowerExpr condition (conditionChild conditionSource)).bind fun value =>
    SnapshotSourceAction.ifValue value (sourceBlockScope yes)
      (SnapshotSourceAction.lowerBlock none [] true yes (yesChild (Core.exprEnv env) yesSource none [] true))
      (SnapshotSourceAction.lowerBlock none [] true no (noChild (Core.exprEnv env) noSource none [] true))).snapshots

end Goose.Lower.Validation
