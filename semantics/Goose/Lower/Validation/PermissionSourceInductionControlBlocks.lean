import Goose.Lower.Validation.PermissionSourceInductionControlExpressions
import Goose.Lower.Validation.PermissionInstructionControlScopes
import Goose.Lower.Validation.SourceStatementTypingBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem permission_source_statements (scope : ScopeId) (stmts : List Stmt)
    {func : Func} {results : List Ty}
    (children : ∀ stmt ∈ stmts, ∀ env, PermissionSourceStatement env func results scope stmt)
    {env output : Core.TEnv} (tables : PermissionSourceTables env results func) {start finish : Nat}
    (source : Core.tyStmts env scope stmts start = .ok (output, finish))
    {first : Nat} {loop : Option LoopCtx} {before after : LS} {result : Unit}
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before)
    (floor : first ≤ before.vals.size)
    (run : lowerStmts loop stmts (lowerEnv env.mod env.vars results) before = (result, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  induction stmts generalizing env start before with
  | nil =>
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact .of_blocks_eq rfl
  | cons stmt rest ih =>
    cases current : before.cur with
    | none =>
      simp only [lowerStmts, bind_run, isLive_none current, Bool.false_eq_true, ite_false, pure_run] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      exact .of_blocks_eq rfl
    | some block =>
      obtain ⟨middleEnv, next, stmtSource, restSource⟩ := tyStmts_cons_children source
      simp only [lowerStmts, bind_run, isLive_run current, ite_true] at run
      let action := lowerStmt loop stmt (lowerEnv env.mod env.vars results) before
      have stmtRun : lowerStmt loop stmt (lowerEnv env.mod env.vars results) before = (action.1, action.2) := rfl
      have restRun : lowerStmts loop rest (lowerEnv env.mod env.vars results) action.2 = (result, after) := run
      let middle := action.2
      have head := children stmt (by simp) env tables stmtSource generated frames floor stmtRun
      have middleGenerated := generated.lowerStmt loop stmt frames.toTargets stmtRun
      have advanced := advB_lowerStmt loop stmt _ _ _ _ stmtRun
      have same := tyStmt_tables stmt stmtSource
      have tailRun : lowerStmts loop rest (lowerEnv middleEnv.mod middleEnv.vars results) middle = (result, after) := by
        simpa only [same.1, same.2.1] using restRun
      have tail := ih (fun child member => children child (by simp [member])) (tables.tyStmt stmtSource)
        restSource middleGenerated (frames.mono advanced.ext) (Nat.le_trans floor advanced.vals) tailRun
      have tail' : NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first middle after := by
        simpa only [same.1, same.2.1] using tail
      exact head.compose_framed tail' restRun (dense_lowerStmts loop rest) (advB_lowerStmts loop rest)
        (types_lowerStmts loop rest) (generatedTargetFrame_lowerStmts loop rest) middleGenerated (frames.mono advanced.ext)

theorem permission_source_block_parts {func : Func} {results : List Ty} (scope : ScopeId)
    (stmts : List Stmt) (value : Option Expr)
    (stmtChildren : ∀ stmt ∈ stmts, ∀ env scope, PermissionSourceStatement env func results scope stmt)
    (valueChild : ∀ expr, value = some expr → ∀ env, PermissionSourceTables env results func →
      PermissionStorageExprChild env func results expr) :
    ∀ env, PermissionSourceBlock env func results (.mk scope stmts value) := by
  intro env tables sourcePre type start finish source first loop pre want before after result generated frames floor transfer run
  obtain ⟨_, declared, output, statementStart, valueStart, declaration, statements, finalValue⟩ :=
    tyBlock_checked_children source
  have declaredTables := declarePre_tables sourcePre declaration
  have outputTables := tyStmts_tables stmts statements
  have declaredAgreement : PermissionSourceTables declared results func :=
    tables.retained declaredTables.2.1 declaredTables.2.2
  have outputAgreement := declaredAgreement.tyStmts statements
  have sameDeclared : lowerEnv declared.mod declared.vars results = lowerEnv env.mod env.vars results := by
    rw [declaredTables.1, declaredTables.2.1]
  have sameOutput : lowerEnv output.mod output.vars results = lowerEnv env.mod env.vars results := by
    rw [outputTables.1, outputTables.2.1, sameDeclared]
  apply lowerBlock_newPermissionInstructions run floor generated frames transfer
  · intro input final lowered generated frames floor
    have lowered' : lowerStmts loop stmts (lowerEnv declared.mod declared.vars results) input = ((), final) := by
      rw [sameDeclared]
      exact lowered
    have trace := permission_source_statements scope stmts (fun stmt member env => stmtChildren stmt member env scope)
      declaredAgreement statements generated frames floor lowered'
    simpa only [declaredTables.1, declaredTables.2.1] using trace
  · intro input final id lowered generated frames floor
    cases value with
    | none =>
      cases want
      · obtain ⟨_, rfl⟩ := pure_eq.mp lowered
        exact .of_blocks_eq rfl
      · exact newPermissions_free_emitDef (by trivial) lowered
    | some expr =>
      have lowered' : lowerExpr expr (lowerEnv output.mod output.vars results) input = (id, final) := by
        rw [sameOutput]
        exact lowered
      have trace := (valueChild expr rfl output outputAgreement finalValue generated lowered').weaken floor
      simpa only [outputTables.1, outputTables.2.1, declaredTables.1, declaredTables.2.1] using trace

#print axioms permission_source_statements
#print axioms permission_source_block_parts

end Goose.Lower.Validation
