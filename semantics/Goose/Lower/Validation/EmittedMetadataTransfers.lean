import Goose.Lower.Validation.EmittedMetadataStorageBindings
import Goose.Lower.Validation.SourceStatementTypingTransfers

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem metadata_source_expressionStatement {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (expr : Expr) (origin : OriginId) (child : EmittedMetadataSourceExpression env results expr) :
    EmittedMetadataSourceStatement env results scope (.expr expr origin) := by
  intro agreement output start finish source loop
  obtain ⟨type, childSource, _⟩ := tyStmt_expr_children source
  exact (((EmittedMetadataAction.lowerExpr expr (child agreement childSource)).withLoop loop).bind fun _ =>
    EmittedMetadataAction.pure _ loop ()).metadata

theorem metadata_source_returnNone (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (origin : OriginId) :
    EmittedMetadataSourceStatement env results scope (.ret none origin) := by
  intro agreement output start finish source loop
  obtain ⟨_, ⟨impl, implAt, resultsAt⟩, _, _⟩ := tyStmt_returnUnit_facts source
  have resultTypes : results = [] := (agreement impl implAt).symm.trans resultsAt
  exact ((EmittedMetadataAction.leaveTo _ loop 0).bind fun _ =>
      EmittedMetadataAction.emitNoSuccessors _ loop (.ret [] (some origin)) rfl (by
        intro before generated live
        apply EmittedTermTyped.ret
        simpa only [lowerEnv, resultTypes] using (TypedValues.nil (state := before)))).metadata

theorem metadata_source_returnSome {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (expr : Expr) (origin : OriginId) (child : EmittedMetadataSourceExpression env results expr) :
    EmittedMetadataSourceStatement env results scope (.ret (some expr) origin) := by
  intro agreement output start finish source loop before result after generated loopBounds loopTypes run checked
  obtain ⟨expected, actual, impl, _, implAt, resultsAt, childSource, permission, _⟩ := tyStmt_return_children source
  have resultTypes : results = [expected] := (agreement impl implAt).symm.trans resultsAt
  let le := lowerEnv env.mod env.vars results
  change (do
    let values ← (do
      let value ← lowerExpr expr
      let coerced ← coerceResult value origin
      pure [coerced])
    leaveTo 0
    emitTerm (.ret values (some origin))) le before = (result, after) at run
  obtain ⟨values, returnedState, prepared, ignored, leftState, leftRun, emitted⟩ := by simpa only [bind_eq] using run
  obtain ⟨value, valueState, valueRun, coerced, coercedState, coercedRun, pureRun⟩ := prepared
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj pureRun
  have valueMetadata := child agreement childSource before value valueState generated trivial trivial valueRun checked
  have valueGenerated := generated.lowerExpr expr valueRun
  have coercedMetadata := (EmittedMetadataAction.coerceResult le none value origin).metadata
    valueState coerced coercedState valueGenerated trivial trivial coercedRun valueMetadata
  have coercedGenerated := valueGenerated.of_runs (dense_coerceResult value origin)
    (generatedTargets_coerceResult none value origin) trivial coercedRun
  have leftMetadata := (EmittedMetadataAction.leaveTo le none 0).metadata
    coercedState ignored leftState coercedGenerated trivial trivial leftRun coercedMetadata
  have finished := leftMetadata.emitTerm (.ret [coerced] (some origin)) (by
    intro live
    have coercedLive : coercedState.cur.isSome = true := by
      have dead := metadata_dead_leaveTo 0
      exact dead.live_before leftRun live
    have valueLive := (metadata_dead_coerceResult value origin).live_before coercedRun coercedLive
    have valueRow := lowerExpr_generated_typed expr childSource valueRun valueLive generated
    cases current : valueState.cur with
    | none => simp [current] at valueLive
    | some block =>
      have targetRow := metadata_coerceResult_typed (le := le) resultTypes valueRow permission current origin
      rw [coercedRun] at targetRow
      have kept := (types_leaveTo 0 le coercedState ignored leftState leftRun) _ _ targetRow
      apply EmittedTermTyped.ret
      rw [show le.results = [expected] from resultTypes]
      exact .cons kept .nil)
  change EmittedMetadata le (emitTerm (.ret [coerced] (some origin)) le leftState).2 at finished
  rw [emitted] at finished
  exact finished

theorem metadata_source_break (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (origin : OriginId) :
    EmittedMetadataSourceStatement env results scope (.brk origin) := by
  intro agreement output start finish source loop
  cases loop with
  | none => exact (EmittedMetadataAction.pure _ none ()).metadata
  | some context =>
    exact ((EmittedMetadataAction.leaveTo _ (some context) context.depth).bind fun _ =>
      EmittedMetadataAction.loopBranch _ (some context) context.breakTo [] (fun _ bounds => bounds.1)).metadata

theorem metadata_source_continue (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (origin : OriginId) :
    EmittedMetadataSourceStatement env results scope (.cont origin) := by
  intro agreement output start finish source loop
  cases loop with
  | none => exact (EmittedMetadataAction.pure _ none ()).metadata
  | some context =>
    cases continuation : context.cont with
    | jump header =>
      have closed : EmittedMetadataAction (lowerEnv env.mod env.vars results) (some context) (emitTerm (.br header [])) :=
        EmittedMetadataAction.loopBranch _ _ header [] (fun state bounds => by simpa only [continuation] using bounds.2)
      simpa only [lowerStmt, continuation] using ((EmittedMetadataAction.leaveTo _ (some context) context.depth).bind fun _ => closed).metadata
    | next header integer counter =>
      have closed : ∀ value, EmittedMetadataAction (lowerEnv env.mod env.vars results) (some context) (emitTerm (.br header [value])) := by
        intro value
        exact EmittedMetadataAction.loopBranch _ _ header [value] (fun state bounds => by simpa only [continuation] using bounds.2)
      simpa only [lowerStmt, continuation] using ((EmittedMetadataAction.leaveTo _ (some context) context.depth).bind fun _ =>
        (EmittedMetadataAction.emitDef _ (some context) (.next integer counter)).bind closed).metadata

theorem metadata_source_abort (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (message : String) (origin : OriginId) :
    EmittedMetadataSourceStatement env results scope (.abort message origin) := by
  intro agreement output start finish source loop
  exact (EmittedMetadataAction.emitNoSuccessors _ loop (.abort .userAbort (some origin)) rfl
    (fun _ _ _ => .abort .userAbort (some origin))).metadata

theorem metadata_source_exit {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (expr : Expr) (origin : OriginId) (child : EmittedMetadataSourceExpression env results expr) :
    EmittedMetadataSourceStatement env results scope (.exit expr origin) := by
  intro agreement output start finish source loop before result after generated loopBounds loopTypes run checked
  obtain ⟨integer, childSource, _⟩ := tyStmt_exit_children source
  change (do let value ← lowerExpr expr; emitTerm (.exit value (some origin)))
    (lowerEnv env.mod env.vars results) before = (result, after) at run
  obtain ⟨value, valueState, valueRun, emitted⟩ := bind_eq.mp run
  have valueMetadata := child agreement childSource before value valueState generated trivial trivial valueRun checked
  have finished := valueMetadata.emitTerm (.exit value (some origin)) (fun live =>
    .exit (lowerExpr_generated_typed expr childSource valueRun live generated))
  simpa only [emitted] using finished

end Goose.Lower.Validation
