import Goose.Lower.Validation.SnapshotContentsSourceLeavesStorage
import Goose.Lower.Validation.SourceStatementTypingTransfers

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem snapshot_source_expressionStatement {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (expr : Expr) (origin : OriginId) (child : SnapshotSourceExpression env results expr) :
    SnapshotSourceStatement env results scope (.expr expr origin) := by
  intro output start finish source loop
  obtain ⟨type, childSource, _⟩ := tyStmt_expr_children source
  exact (((SnapshotSourceAction.lowerExpr expr (child childSource)).withLoop loop).bind fun _ =>
    SnapshotSourceAction.pure _ loop ()).snapshots

theorem snapshot_source_returnNone (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (origin : OriginId) :
    SnapshotSourceStatement env results scope (.ret none origin) := by
  intro output start finish source loop
  exact ((SnapshotSourceAction.pure _ loop ([] : List ValueId)).bind fun values =>
    (SnapshotSourceAction.leaveTo _ loop 0).bind fun _ =>
      SnapshotSourceAction.emitTerm _ loop (.ret values (some origin)) rfl).snapshots

theorem snapshot_source_returnSome {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (expr : Expr) (origin : OriginId) (child : SnapshotSourceExpression env results expr) :
    SnapshotSourceStatement env results scope (.ret (some expr) origin) := by
  intro output start finish source loop
  obtain ⟨expected, actual, impl, _, _, _, childSource, _, _⟩ := tyStmt_return_children source
  exact ((((SnapshotSourceAction.lowerExpr expr (child childSource)).withLoop loop).bind fun value =>
    (SnapshotSourceAction.coerceResult _ loop value origin).bind fun coerced =>
      SnapshotSourceAction.pure _ loop [coerced]).bind fun values =>
        (SnapshotSourceAction.leaveTo _ loop 0).bind fun _ =>
          SnapshotSourceAction.emitTerm _ loop (.ret values (some origin)) rfl).snapshots

theorem snapshot_source_break (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (origin : OriginId) :
    SnapshotSourceStatement env results scope (.brk origin) := by
  intro output start finish source loop
  cases loop with
  | none => exact SnapshotTraceRun.pure ()
  | some context =>
    exact ((SnapshotSourceAction.leaveTo _ (some context) context.depth).bind fun _ =>
      SnapshotSourceAction.loopBranch _ (some context) context.breakTo [] (fun _ bounds => bounds.1) (Or.inl rfl)).snapshots

theorem snapshot_source_continue (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (origin : OriginId) :
    SnapshotSourceStatement env results scope (.cont origin) := by
  intro output start finish source loop
  cases loop with
  | none => exact SnapshotTraceRun.pure ()
  | some context =>
    cases continuation : context.cont with
    | jump header =>
      have closed : SnapshotSourceAction (lowerEnv env.mod env.vars results) (some context) (emitTerm (.br header [])) :=
        SnapshotSourceAction.loopBranch _ _ header []
          (fun state bounds => by simpa only [continuation] using bounds.2)
          (by simp [LoopBuilderFrameTarget, continuation])
      simpa only [lowerStmt, continuation] using ((SnapshotSourceAction.leaveTo _ (some context) context.depth).bind fun _ => closed).snapshots
    | next header integer counter =>
      have closed : ∀ value, SnapshotSourceAction (lowerEnv env.mod env.vars results) (some context) (emitTerm (.br header [value])) := by
        intro value
        exact SnapshotSourceAction.loopBranch _ _ header [value]
          (fun state bounds => by simpa only [continuation] using bounds.2)
          (by simp [LoopBuilderFrameTarget, continuation])
      simpa only [lowerStmt, continuation] using ((SnapshotSourceAction.leaveTo _ (some context) context.depth).bind fun _ =>
        (SnapshotSourceAction.emitDef _ (some context) (.next integer counter) (by intros; intro h; cases h)).bind closed).snapshots

theorem snapshot_source_abort (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (message : String) (origin : OriginId) :
    SnapshotSourceStatement env results scope (.abort message origin) := by
  intro output start finish source loop
  exact (SnapshotSourceAction.emitTerm _ loop (.abort .userAbort (some origin)) rfl).snapshots

theorem snapshot_source_exit {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (expr : Expr) (origin : OriginId) (child : SnapshotSourceExpression env results expr) :
    SnapshotSourceStatement env results scope (.exit expr origin) := by
  intro output start finish source loop
  obtain ⟨integer, childSource, _⟩ := tyStmt_exit_children source
  exact (((SnapshotSourceAction.lowerExpr expr (child childSource)).withLoop loop).bind fun value =>
    SnapshotSourceAction.emitTerm _ loop (.exit value (some origin)) rfl).snapshots

theorem snapshot_source_printArguments {le : LEnv} (args : List PrintArg)
    (children : ∀ expr, PrintArg.expr expr ∈ args → SnapshotTraceRun le none (lowerExpr expr)) :
    SnapshotTraceRun le none (lowerPrintArgs args) := by
  induction args with
  | nil => exact SnapshotTraceRun.pure []
  | cons arg rest inductionHypothesis =>
    have tail := inductionHypothesis (fun expr member => children expr (by simp [member]))
    cases arg with
    | text text =>
      exact ((SnapshotSourceAction.mk tail (dense_lowerPrintArgs rest) (advB_lowerPrintArgs rest)
        (generatedTargets_lowerPrintArgs none rest) (types_lowerPrintArgs rest) (generatedTargetFrame_lowerPrintArgs none rest)).bind
          fun values => SnapshotSourceAction.pure _ none (.text text :: values)).snapshots
    | expr expr =>
      exact ((SnapshotSourceAction.lowerExpr expr (children expr (by simp))).bind fun value =>
        (SnapshotSourceAction.mk tail (dense_lowerPrintArgs rest) (advB_lowerPrintArgs rest)
          (generatedTargets_lowerPrintArgs none rest) (types_lowerPrintArgs rest) (generatedTargetFrame_lowerPrintArgs none rest)).bind
            fun values => SnapshotSourceAction.pure _ none (.val value :: values)).snapshots

theorem snapshot_source_print {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (args : List PrintArg) (origin : OriginId)
    (children : ∀ expr, PrintArg.expr expr ∈ args → SnapshotSourceExpression env results expr) :
    SnapshotSourceStatement env results scope (.print args origin) := by
  intro output start finish source loop
  have printSource := (tyStmt_print_children source).1
  have parts := snapshot_source_printArguments args (fun expr member => by
    obtain ⟨type, childStart, childFinish, childSource, _⟩ := tyPrintArgs_expr_children printSource member
    exact children expr member childSource)
  exact (((SnapshotSourceAction.mk parts (dense_lowerPrintArgs args) (advB_lowerPrintArgs args)
    (generatedTargets_lowerPrintArgs none args) (types_lowerPrintArgs args) (generatedTargetFrame_lowerPrintArgs none args)).withLoop loop).bind
      fun values => SnapshotSourceAction.emitEffect _ loop (.print values (some origin))).snapshots

end Goose.Lower.Validation
