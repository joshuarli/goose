import Goose.Lower.Validation.EmittedMetadataStaticProfileSourceStorage
import Goose.Lower.Validation.SourceStatementTypingTransfers

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem profile_source_expressionStatement {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (expr : Expr) (origin : OriginId) (child : EmittedProfileSourceExpression env results expr) :
    EmittedProfileSourceStatement env results scope (.expr expr origin) := by
  intro output start finish source loop
  obtain ⟨type, childSource, _⟩ := tyStmt_expr_children source
  exact (child childSource).bind fun _ => EmittedProfileRun.pure ()

theorem profile_source_returnNone (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (origin : OriginId) :
    EmittedProfileSourceStatement env results scope (.ret none origin) := by
  intro output start finish source loop
  exact (EmittedProfileRun.pure ([] : List ValueId)).bind fun values =>
    (EmittedProfileRun.leaveTo 0).bind fun _ => EmittedProfileRun.emitTerm (.ret values (some origin)) trivial

theorem profile_source_returnSome {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (expr : Expr) (origin : OriginId) (child : EmittedProfileSourceExpression env results expr) :
    EmittedProfileSourceStatement env results scope (.ret (some expr) origin) := by
  intro output start finish source loop
  obtain ⟨expected, actual, impl, _, _, _, childSource, _, _⟩ := tyStmt_return_children source
  exact ((child childSource).bind fun value =>
    (EmittedProfileRun.coerceResult value origin).bind fun coerced =>
      EmittedProfileRun.pure [coerced]).bind fun values =>
        (EmittedProfileRun.leaveTo 0).bind fun _ => EmittedProfileRun.emitTerm (.ret values (some origin)) trivial

theorem profile_source_break (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (origin : OriginId) :
    EmittedProfileSourceStatement env results scope (.brk origin) := by
  intro output start finish source loop
  cases loop with
  | none => exact EmittedProfileRun.pure ()
  | some context => exact (EmittedProfileRun.leaveTo context.depth).bind fun _ =>
      EmittedProfileRun.emitTerm (.br context.breakTo []) trivial

theorem profile_source_continue (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (origin : OriginId) :
    EmittedProfileSourceStatement env results scope (.cont origin) := by
  intro output start finish source loop
  cases loop with
  | none => exact EmittedProfileRun.pure ()
  | some context =>
    cases continuation : context.cont with
    | jump header =>
      simpa only [lowerStmt, continuation] using
        (EmittedProfileRun.leaveTo (profile := env.mod.profile) (le := lowerEnv env.mod env.vars results) context.depth).bind
          (fun _ => EmittedProfileRun.emitTerm (.br header []) trivial)
    | next header integer counter =>
      simpa only [lowerStmt, continuation] using
        (EmittedProfileRun.leaveTo (profile := env.mod.profile) (le := lowerEnv env.mod env.vars results) context.depth).bind
          (fun _ => (EmittedProfileRun.emitDef (.next integer counter) (fun _ => trivial)).bind fun value =>
            EmittedProfileRun.emitTerm (.br header [value]) trivial)

theorem profile_source_abort (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (message : String) (origin : OriginId) :
    EmittedProfileSourceStatement env results scope (.abort message origin) := by
  intro output start finish source loop
  exact EmittedProfileRun.emitTerm (.abort .userAbort (some origin)) (by simp [EmittedProfileInst])

theorem profile_source_exit {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (expr : Expr) (origin : OriginId) (child : EmittedProfileSourceExpression env results expr) :
    EmittedProfileSourceStatement env results scope (.exit expr origin) := by
  intro output start finish source loop
  obtain ⟨integer, childSource, _⟩ := tyStmt_exit_children source
  exact (child childSource).bind fun value => EmittedProfileRun.emitTerm (.exit value (some origin)) trivial

theorem profile_source_printArguments {profile : ArtifactProfile} {le : LEnv} (args : List PrintArg)
    (children : ∀ expr, PrintArg.expr expr ∈ args → EmittedProfileRun profile le (lowerExpr expr)) :
    EmittedProfileRun profile le (lowerPrintArgs args) := by
  induction args with
  | nil => exact EmittedProfileRun.pure []
  | cons arg rest inductionHypothesis =>
    have tail := inductionHypothesis (fun expr member => children expr (by simp [member]))
    cases arg with
    | text text => exact tail.bind fun values => EmittedProfileRun.pure (.text text :: values)
    | expr expr =>
      exact (children expr (by simp)).bind fun value =>
        tail.bind fun values => EmittedProfileRun.pure (.val value :: values)

theorem profile_source_print {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (args : List PrintArg) (origin : OriginId)
    (children : ∀ expr, PrintArg.expr expr ∈ args → EmittedProfileSourceExpression env results expr) :
    EmittedProfileSourceStatement env results scope (.print args origin) := by
  intro output start finish source loop
  have printSource := (tyStmt_print_children source).1
  have parts := profile_source_printArguments args (fun expr member => by
    obtain ⟨type, childStart, childFinish, childSource, _⟩ := tyPrintArgs_expr_children printSource member
    exact children expr member childSource)
  exact parts.bind fun values => EmittedProfileRun.emitEffect (.print values (some origin)) trivial

end Goose.Lower.Validation
