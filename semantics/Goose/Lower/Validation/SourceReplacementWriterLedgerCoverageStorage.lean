import Goose.Lower.Validation.SourceReplacementWriterLedgerCoverageActions

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem let_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (slot : VarId) (expression : Expr) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.letS slot expression origin)) env before := by
  intro neutral children events
  change At property env before (lowerStmt loop (.letS slot expression origin))
  simp only [lowerStmt]
  apply At.bind (children 0 (.expression expression) before rfl)
  apply At.bind (At.neutral neutral (neutral_coerceSlot _ _ _))
  apply EmissionsCovered.effect events
  intro live
  simp [Fragment.emissions,effectEmission,live]

theorem assign_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (place : Place) (expression : Expr) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.assign place expression origin)) env before := by
  intro neutral children events
  change At property env before (lowerStmt loop (.assign place expression origin))
  simp only [lowerStmt]
  apply At.bind (children 0 (.place place) before rfl)
  apply At.bind (children 1 (.expression expression) (lowerPlace place env before).2 rfl)
  apply EmissionsCovered.effect events
  intro live
  simp [Fragment.emissions,effectEmission,live]

theorem assignOp_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (operation : BinOp) (place : Place) (expression : Expr) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.assignOp operation place expression origin)) env before := by
  intro neutral children events
  change At property env before (lowerStmt loop (.assignOp operation place expression origin))
  simp only [lowerStmt]
  apply At.bind (children 0 (.place place) before rfl)
  apply At.bind (At.neutralDef neutral (by intro; simp [NeutralInstruction,WriterInstruction]))
  apply At.bind (children 1 (.expression expression) _ rfl)
  apply At.bind (At.neutral neutral (neutral_intTyOf _))
  apply At.bind (At.neutralDef neutral (by intro; simp [NeutralInstruction,WriterInstruction]))
  apply EmissionsCovered.effect events
  intro live
  simp [Fragment.emissions,effectEmission,live]

theorem rebind_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (slot : VarId) (expression : Expr) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.rebind slot expression origin)) env before := by
  intro neutral children events
  change At property env before (lowerStmt loop (.rebind slot expression origin))
  simp only [lowerStmt]
  apply At.bind (children 0 (.expression expression) before rfl)
  apply At.bind (At.neutral neutral (neutral_coerceSlot _ _ _))
  apply At.bind (At.neutralDef neutral (by intro; simp [NeutralInstruction,WriterInstruction]))
  apply EmissionsCovered.effect events
  intro live
  simp [Fragment.emissions,effectEmission,live]

theorem assignWhole_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (place : Place) (expression : Expr) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.assignWhole place expression origin)) env before := by
  intro neutral children events
  change At property env before (lowerStmt loop (.assignWhole place expression origin))
  simp only [lowerStmt]
  apply At.bind (children 0 (.place place) before rfl)
  apply At.bind (At.neutralEffect neutral (by simp [NeutralInstruction,WriterInstruction]))
  apply At.bind (children 1 (.expression expression) _ rfl)
  apply EmissionsCovered.effect events
  intro live
  simp [Fragment.emissions,effectEmission,live]

#print axioms let_emission_coverage
#print axioms assign_emission_coverage
#print axioms assignOp_emission_coverage
#print axioms rebind_emission_coverage
#print axioms assignWhole_emission_coverage

end Goose.Lower.Validation.SourceReplacementWriterLedger
