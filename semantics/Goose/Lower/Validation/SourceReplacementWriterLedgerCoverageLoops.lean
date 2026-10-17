import Goose.Lower.Validation.SourceReplacementWriterLedgerCoverageControls

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem ifStatement_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (condition : Expr) (yes : Core.Block) (no : Option Core.Block) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.ifS condition yes no origin)) env before := by
  cases no with
  | none =>
    intro neutral children events
    change At property env before (lowerStmt loop (.ifS condition yes none origin))
    simp only [lowerStmt]
    apply At.bind (children 0 (.expression condition) before rfl)
    apply At.whenLive
    intro block current
    apply At.bind (At.of_run (emitsOnly_fork property (fun term => neutral _ (by simp [WriterInstruction])) _))
    apply At.bind (At.of_run (emitsOnly_setCur _ _))
    apply At.bind
    · apply children 1 (.block loop [] false yes) _
      simp [Fragment.child?,Fragment.children,branchChildren,current]
    · apply At.bind (At.term _ neutral)
      exact At.of_run (emitsOnly_setCur _ _)
  | some no =>
    intro neutral children events
    change At property env before (lowerStmt loop (.ifS condition yes (some no) origin))
    simp only [lowerStmt]
    apply At.bind (children 0 (.expression condition) before rfl)
    apply At.whenLive
    intro block current
    apply At.bind (At.of_run (emitsOnly_fork property (fun term => neutral _ (by simp [WriterInstruction])) _))
    apply At.bind (At.of_run (emitsOnly_setCur _ _))
    apply At.bind
    · apply children 1 (.block loop [] false yes) _
      simp [Fragment.child?,Fragment.children,branchChildren,current]
    · apply At.bind (At.of_blocks rfl)
      apply At.bind (At.of_run (emitsOnly_setCur _ _))
      apply At.bind
      · apply children 2 (.block loop [] false no) _
        simp [Fragment.child?,Fragment.children,branchChildren,current,curBlock_run]
      · apply At.bind (At.of_blocks rfl)
        exact At.of_run (ReplacementContentFlowSource.emitsOnly_joinArms
          (fun term => neutral _ (by simp [WriterInstruction])) _ _)

theorem while_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (condition : Expr) (body : Core.Block) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.while condition body origin)) env before := by
  intro neutral children events
  change At property env before (lowerStmt loop (.while condition body origin))
  simp only [lowerStmt,lowerWhile]
  apply At.bind (At.of_run (emitsOnly_newBlock _ _))
  apply At.bind (At.term _ neutral)
  apply At.bind (At.of_run (emitsOnly_setCur _ _))
  apply At.bind (children 0 (.expression condition) _ rfl)
  apply At.whenLive
  intro block current
  simp only [loopBody]
  apply At.bind (At.of_blocks rfl)
  apply At.bind (At.of_run (emitsOnly_fork property (fun term => neutral _ (by simp [WriterInstruction])) _))
  apply At.bind (At.of_run (emitsOnly_setCur _ _))
  apply At.bind
  · apply children 1 (.block _ [] false body) _
    simp [Fragment.child?,Fragment.children,whileChildren,current,get_apply]
  · apply At.bind (At.term _ neutral)
    exact At.of_run (emitsOnly_setCur _ _)

theorem neutral_rangeBack (type : IntTy) (counter : ValueId) (header : BlockId) :
    EmitsOnlyRun NeutralInstruction (rangeBack type counter header) := by
  unfold rangeBack
  apply EmitsOnlyRun.bind (EmitsOnlyRun.unchanged (fun _ _ => rfl))
  intro live
  cases live with
  | false => exact .pure _ _
  | true =>
    exact (neutral_emitDef _ (by intro; simp [NeutralInstruction,WriterInstruction])).bind fun _ =>
      emitsOnly_emitTerm _ (by simp [NeutralInstruction,WriterInstruction])

theorem range_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (variableId : VarId) (low high : Expr) (body : Core.Block) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.forRange variableId low high body origin)) env before := by
  intro neutral children events
  change At property env before (lowerStmt loop (.forRange variableId low high body origin))
  simp only [lowerStmt,lowerRange,loopBody]
  apply At.bind (children 0 (.expression low) before rfl)
  apply At.bind (children 1 (.expression high) _ rfl)
  apply At.whenLive
  intro block current
  apply At.bind (At.neutral neutral (neutral_intTyOf _))
  apply At.bind (At.of_run (emitsOnly_newBlock _ _))
  apply At.bind (At.term _ neutral)
  apply At.bind (At.of_run (emitsOnly_setCur _ _))
  apply At.bind (At.neutralDef neutral (by intro; simp [NeutralInstruction,WriterInstruction]))
  apply At.bind (At.of_blocks rfl)
  apply At.bind (At.of_run (emitsOnly_fork property (fun term => neutral _ (by simp [WriterInstruction])) _))
  apply At.bind (At.of_run (emitsOnly_setCur _ _))
  apply At.bind
  · apply children 2 (.block _ _ false body) _
    simp [Fragment.child?,Fragment.children,rangeChild,current,get_apply,intTyOf_state]
  · apply At.bind (At.neutral neutral (neutral_rangeBack _ _ _))
    exact At.of_run (emitsOnly_setCur _ _)

#print axioms ifStatement_emission_coverage
#print axioms while_emission_coverage
#print axioms range_emission_coverage

end Goose.Lower.Validation.SourceReplacementWriterLedger
