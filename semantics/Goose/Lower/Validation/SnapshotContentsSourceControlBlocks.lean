import Goose.Lower.Validation.SnapshotContentsSourceControlActions
import Goose.Lower.Validation.SourceStatementTypingBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem snapshot_source_statements {results : List Ty} (scope : ScopeId) (stmts : List Stmt)
    (children : ∀ stmt ∈ stmts, ∀ env scope, SnapshotSourceStatement env results scope stmt)
    {env output : Core.TEnv} {start finish : Nat}
    (source : Core.tyStmts env scope stmts start = .ok (output, finish)) (loop : Option LoopCtx) :
    SnapshotTraceRun (lowerEnv env.mod env.vars results) loop (lowerStmts loop stmts) := by
  induction stmts generalizing env start with
  | nil => exact SnapshotTraceRun.pure ()
  | cons stmt rest ih =>
    obtain ⟨middle, next, headTyped, tailTyped⟩ := tyStmts_cons_children source
    have tables := tyStmt_tables stmt headTyped
    have same : lowerEnv middle.mod middle.vars results = lowerEnv env.mod env.vars results := by
      rw [tables.1, tables.2.1]
    have head := children stmt (by simp) env scope headTyped loop
    have tail := ih (fun child member => children child (List.mem_cons_of_mem _ member)) tailTyped
    rw [same] at tail
    unfold lowerStmts
    refine ((SnapshotSourceAction.isLive _ loop).bind fun active => ?_).snapshots
    cases active
    · exact SnapshotSourceAction.pure _ loop ()
    · exact (SnapshotSourceAction.lowerStmt loop stmt head).bind fun _ =>
        SnapshotSourceAction.lowerStmts loop rest tail

theorem snapshot_source_block_parts {results : List Ty} (scope : ScopeId)
    (stmts : List Stmt) (value : Option Expr)
    (stmtChildren : ∀ stmt ∈ stmts, ∀ env scope, SnapshotSourceStatement env results scope stmt)
    (valueChild : ∀ expr, value = some expr → ∀ env, SnapshotSourceExpression env results expr) :
    ∀ env, SnapshotSourceBlock env results (.mk scope stmts value) := by
  intro env sourcePre type start finish source loop pre want
  obtain ⟨_, declared, output, statementStart, valueStart, declaration, statements, finalValue⟩ :=
    tyBlock_checked_children source
  have declaredTables := declarePre_tables sourcePre declaration
  have outputTables := tyStmts_tables stmts statements
  have sameDeclared : lowerEnv declared.mod declared.vars results = lowerEnv env.mod env.vars results := by
    rw [declaredTables.1, declaredTables.2.1]
  have sameOutput : lowerEnv output.mod output.vars results = lowerEnv env.mod env.vars results := by
    rw [outputTables.1, outputTables.2.1, sameDeclared]
  have statementTrace := snapshot_source_statements scope stmts stmtChildren statements loop
  rw [sameDeclared] at statementTrace
  have valueTrace : SnapshotSourceAction (lowerEnv env.mod env.vars results) loop (lowerBlockValue want value) := by
    cases value with
    | none =>
      cases want
      · exact SnapshotSourceAction.pure _ loop 0
      · exact SnapshotSourceAction.emitDef _ loop .constUnit (by intros; intro impossible; cases impossible)
    | some expr =>
      have checked := (SnapshotSourceAction.lowerExpr expr (valueChild expr rfl output finalValue)).withLoop loop
      rw [sameOutput] at checked
      exact checked
  unfold lowerBlock
  exact ((SnapshotSourceAction.emitEffect _ loop (.enter scope)).bind fun _ =>
    SnapshotSourceAction.inScope scope ((SnapshotSourceAction.initSlots _ loop pre).bind fun _ =>
      (SnapshotSourceAction.lowerStmts loop stmts statementTrace).bind fun _ => valueTrace.bind fun result =>
        (SnapshotSourceAction.emitEffect _ loop (.leave scope)).bind fun _ =>
          SnapshotSourceAction.pure _ loop result)).snapshots

theorem snapshot_source_blockExpression {results : List Ty} (body : Core.Block)
    (child : ∀ env, SnapshotSourceBlock env results body) :
    ∀ env, SnapshotSourceExpression env results (.blockE body) := by
  intro env type start finish source
  exact child (Core.exprEnv env) source none [] true

end Goose.Lower.Validation
