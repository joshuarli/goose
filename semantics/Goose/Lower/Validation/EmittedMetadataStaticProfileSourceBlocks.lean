import Goose.Lower.Validation.EmittedMetadataStaticProfileSourceTransfers
import Goose.Lower.Validation.SourceStatementTypingBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem profile_source_statements {results : List Ty} (scope : ScopeId) (stmts : List Stmt)
    (children : ∀ stmt ∈ stmts, ∀ env scope, EmittedProfileSourceStatement env results scope stmt)
    {env output : Core.TEnv} {start finish : Nat}
    (source : Core.tyStmts env scope stmts start = .ok (output, finish)) (loop : Option LoopCtx) :
    EmittedProfileRun env.mod.profile (lowerEnv env.mod env.vars results) (lowerStmts loop stmts) := by
  induction stmts generalizing env start with
  | nil => exact EmittedProfileRun.pure ()
  | cons stmt rest ih =>
    obtain ⟨middle, next, headTyped, tailTyped⟩ := tyStmts_cons_children source
    have tables := tyStmt_tables stmt headTyped
    have same : lowerEnv middle.mod middle.vars results = lowerEnv env.mod env.vars results := by
      rw [tables.1, tables.2.1]
    have head := children stmt (by simp) env scope headTyped loop
    have tail := ih (fun child member => children child (List.mem_cons_of_mem _ member)) tailTyped
    rw [same, tables.1] at tail
    unfold lowerStmts
    refine ((EmittedProfileRun.isLive).bind fun active => ?_)
    cases active
    · exact EmittedProfileRun.pure ()
    · exact head.bind fun _ =>
        tail

theorem profile_source_block_parts {results : List Ty} (scope : ScopeId)
    (stmts : List Stmt) (value : Option Expr)
    (stmtChildren : ∀ stmt ∈ stmts, ∀ env scope, EmittedProfileSourceStatement env results scope stmt)
    (valueChild : ∀ expr, value = some expr → ∀ env, EmittedProfileSourceExpression env results expr) :
    ∀ env, EmittedProfileSourceBlock env results (.mk scope stmts value) := by
  intro env sourcePre type start finish source loop pre want
  obtain ⟨_, declared, output, statementStart, valueStart, declaration, statements, finalValue⟩ :=
    tyBlock_checked_children source
  have declaredTables := declarePre_tables sourcePre declaration
  have outputTables := tyStmts_tables stmts statements
  have sameDeclared : lowerEnv declared.mod declared.vars results = lowerEnv env.mod env.vars results := by
    rw [declaredTables.1, declaredTables.2.1]
  have sameOutput : lowerEnv output.mod output.vars results = lowerEnv env.mod env.vars results := by
    rw [outputTables.1, outputTables.2.1, sameDeclared]
  have statementTrace := profile_source_statements scope stmts stmtChildren statements loop
  rw [sameDeclared, declaredTables.1] at statementTrace
  have valueTrace : EmittedProfileRun env.mod.profile (lowerEnv env.mod env.vars results) (lowerBlockValue want value) := by
    cases value with
    | none =>
      cases want
      · exact EmittedProfileRun.pure 0
      · exact EmittedProfileRun.emitDef .constUnit (by intro; trivial)
    | some expr =>
      have checked := (valueChild expr rfl output finalValue)
      rw [sameOutput, outputTables.1, declaredTables.1] at checked
      exact checked
  unfold lowerBlock
  exact ((EmittedProfileRun.emitEffect (.enter scope) trivial).bind fun _ =>
    EmittedProfileRun.inScope scope ((EmittedProfileRun.initSlots pre).bind fun _ =>
      statementTrace.bind fun _ => valueTrace.bind fun result =>
        (EmittedProfileRun.emitEffect (.leave scope) trivial).bind fun _ =>
          EmittedProfileRun.pure result))

theorem profile_source_blockExpression {results : List Ty} (body : Core.Block)
    (child : ∀ env, EmittedProfileSourceBlock env results body) :
    ∀ env, EmittedProfileSourceExpression env results (.blockE body) := by
  intro env type start finish source
  exact child (Core.exprEnv env) source none [] true

end Goose.Lower.Validation
