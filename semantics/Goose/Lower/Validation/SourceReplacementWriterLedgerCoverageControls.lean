import Goose.Lower.Validation.SourceReplacementWriterLedgerCoverageActions

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem and_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (left right : Expr) : EmissionCoverage property (.expression (.and left right)) env before := by
  intro neutral children events
  change At property env before (lowerExpr (.and left right))
  simp only [lowerExpr,shortCircuit]
  apply At.bind (children 0 (.expression left) before rfl)
  apply At.whenLive
  intro block current
  apply At.bind (At.of_run (emitsOnly_scFork property (fun term => neutral _ (by simp [WriterInstruction])) _ _))
  apply At.bind (At.of_run (emitsOnly_setCur _ _))
  apply At.bind
  · apply children 1 (.expression right) _
    simp [Fragment.child?,Fragment.children,shortCircuitChild,current]
  · apply At.bind (At.term _ neutral)
    apply At.bind (At.of_run (emitsOnly_setCur _ _))
    exact At.pure _ _ _ _

theorem or_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (left right : Expr) : EmissionCoverage property (.expression (.or left right)) env before := by
  intro neutral children events
  change At property env before (lowerExpr (.or left right))
  simp only [lowerExpr,shortCircuit]
  apply At.bind (children 0 (.expression left) before rfl)
  apply At.whenLive
  intro block current
  apply At.bind (At.of_run (emitsOnly_scFork property (fun term => neutral _ (by simp [WriterInstruction])) _ _))
  apply At.bind (At.of_run (emitsOnly_setCur _ _))
  apply At.bind
  · apply children 1 (.expression right) _
    simp [Fragment.child?,Fragment.children,shortCircuitChild,current]
  · apply At.bind (At.term _ neutral)
    apply At.bind (At.of_run (emitsOnly_setCur _ _))
    exact At.pure _ _ _ _

theorem blockExpression_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (block : Core.Block) : EmissionCoverage property (.expression (.blockE block)) env before := by
  intro neutral children events
  exact children 0 (.block none [] true block) before rfl

theorem ifExpression_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (condition : Expr) (yes no : Core.Block) :
    EmissionCoverage property (.expression (.ifE condition yes no)) env before := by
  intro neutral children events
  change At property env before (lowerExpr (.ifE condition yes no))
  simp only [lowerExpr]
  apply At.bind (children 0 (.expression condition) before rfl)
  apply At.whenLive
  intro block current
  apply At.bind (At.of_run (emitsOnly_fork property (fun term => neutral _ (by simp [WriterInstruction])) _))
  apply At.bind (At.of_run (emitsOnly_setCur _ _))
  apply At.bind
  · apply children 1 (.block none [] true yes) _
    simp [Fragment.child?,Fragment.children,branchChildren,current]
  · apply At.bind (At.of_blocks rfl)
    apply At.bind (At.of_run (emitsOnly_setCur _ _))
    apply At.bind
    · apply children 2 (.block none [] true no) _
      simp [Fragment.child?,Fragment.children,branchChildren,current,curBlock_run]
    · apply At.bind (At.of_blocks rfl)
      apply At.bind (At.of_run (emitsOnly_joinValue property (fun term => neutral _ (by simp [WriterInstruction])) _ _ _ _))
      apply At.bind
      · apply At.of_blocks
        rw [recordValueRootRecipe_run]
      · exact At.pure _ _ _ _

theorem assert_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (expression : Expr) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.assertS expression origin)) env before := by
  intro neutral children events
  change At property env before (lowerStmt loop (.assertS expression origin))
  simp only [lowerStmt]
  apply At.bind (children 0 (.expression expression) before rfl)
  apply At.whenLive
  intro block current
  apply At.bind (At.of_run (emitsOnly_fork property (fun term => neutral _ (by simp [WriterInstruction])) _))
  apply At.bind (At.of_run (emitsOnly_setCur _ _))
  apply At.bind (At.term _ neutral)
  exact At.of_run (emitsOnly_setCur _ _)

#print axioms and_emission_coverage
#print axioms or_emission_coverage
#print axioms ifExpression_emission_coverage
#print axioms assert_emission_coverage

end Goose.Lower.Validation.SourceReplacementWriterLedger
