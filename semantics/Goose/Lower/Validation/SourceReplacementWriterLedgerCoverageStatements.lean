import Goose.Lower.Validation.SourceReplacementWriterLedgerCoverageStorage
import Goose.Lower.Validation.SourceReplacementWriterLedgerCoverageBlocks

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem neutral_leaveAll (scopes : List ScopeId) : EmitsOnlyRun NeutralInstruction (leaveAll scopes) := by
  induction scopes with
  | nil => exact .pure _ _
  | cons scope rest ih =>
    exact (emitsOnly_emitEffect _ (by simp [NeutralInstruction,WriterInstruction])).bind fun _ => ih

theorem neutral_leaveTo (depth : Nat) : EmitsOnlyRun NeutralInstruction (leaveTo depth) := by
  unfold leaveTo
  exact (EmitsOnlyRun.unchanged (fun _ _ => rfl)).bind fun state => neutral_leaveAll _

theorem expressionStatement_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (expression : Expr) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.expr expression origin)) env before := by
  intro neutral children events
  exact At.bind (children 0 (.expression expression) before rfl) (At.pure _ _ _ _)

theorem append_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (place : Place) (view : View) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.append place view origin)) env before := by
  intro neutral children events
  change At property env before (lowerStmt loop (.append place view origin))
  simp only [lowerStmt]
  apply At.bind (children 0 (.place place) before rfl)
  apply At.bind (children 1 (.view view) _ rfl)
  exact At.neutralEffect neutral (by simp [NeutralInstruction,WriterInstruction])

theorem popN_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (place : Place) (expression : Expr) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.popN place expression origin)) env before := by
  intro neutral children events
  change At property env before (lowerStmt loop (.popN place expression origin))
  simp only [lowerStmt]
  apply At.bind (children 0 (.place place) before rfl)
  apply At.bind (children 1 (.expression expression) _ rfl)
  exact At.neutralEffect neutral (by simp [NeutralInstruction,WriterInstruction])

theorem resize_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (place : Place) (size : Expr) (fill : Option Expr) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.resize place size fill origin)) env before := by
  cases fill with
  | none =>
    intro neutral children events
    change At property env before (lowerStmt loop (.resize place size none origin))
    simp only [lowerStmt]
    apply At.bind (children 0 (.place place) before rfl)
    apply At.bind (children 1 (.expression size) _ rfl)
    exact At.bind (At.pure _ _ _ _) (At.neutralEffect neutral (by simp [NeutralInstruction,WriterInstruction]))
  | some expression =>
    intro neutral children events
    change At property env before (lowerStmt loop (.resize place size (some expression) origin))
    simp only [lowerStmt]
    apply At.bind (children 0 (.place place) before rfl)
    apply At.bind (children 1 (.expression size) _ rfl)
    apply At.bind (children 2 (.expression expression) _ rfl)
    exact At.bind (At.pure _ _ _ _) (At.neutralEffect neutral (by simp [NeutralInstruction,WriterInstruction]))

theorem clear_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (place : Place) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.clear place origin)) env before := by
  intro neutral children events
  exact At.bind (children 0 (.place place) before rfl)
    (At.neutralEffect neutral (by simp [NeutralInstruction,WriterInstruction]))

theorem return_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (expression : Option Expr) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.ret expression origin)) env before := by
  cases expression with
  | none =>
    intro neutral children events
    change At property env before (lowerStmt loop (.ret none origin))
    simp only [lowerStmt]
    apply At.bind (At.pure _ _ _ _)
    exact At.bind (At.neutral neutral (neutral_leaveTo _)) (At.term _ neutral)
  | some expression =>
    intro neutral children events
    change At property env before (lowerStmt loop (.ret (some expression) origin))
    simp only [lowerStmt]
    apply At.bind (children 0 (.expression expression) before rfl)
    apply At.bind (At.neutral neutral (neutral_coerceResult _ _))
    apply At.bind (At.pure _ _ _ _)
    exact At.bind (At.neutral neutral (neutral_leaveTo _)) (At.term _ neutral)

theorem break_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.brk origin)) env before := by
  intro neutral children events
  cases loop with
  | none => exact At.pure _ _ _ _
  | some context =>
    exact At.bind (At.neutral neutral (neutral_leaveTo _)) (At.term _ neutral)

theorem continue_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.cont origin)) env before := by
  intro neutral children events
  cases loop with
  | none => exact At.pure _ _ _ _
  | some context =>
    change At property env before (lowerStmt (some context) (.cont origin))
    simp only [lowerStmt]
    apply At.bind (At.neutral neutral (neutral_leaveTo _))
    cases context.cont with
    | jump header => exact At.term _ neutral
    | next header type counter =>
      exact At.bind (At.neutralDef neutral (by intro; simp [NeutralInstruction,WriterInstruction])) (At.term _ neutral)

theorem abort_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (message : String) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.abort message origin)) env before := by
  intro neutral children events
  exact At.term _ neutral

theorem exit_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (expression : Expr) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.exit expression origin)) env before := by
  intro neutral children events
  exact At.bind (children 0 (.expression expression) before rfl) (At.term _ neutral)

#print axioms resize_emission_coverage
#print axioms return_emission_coverage
#print axioms continue_emission_coverage

end Goose.Lower.Validation.SourceReplacementWriterLedger
