import Goose.Lower.Validation.EmittedTypingSourceActions
import Goose.Lower.Validation.EmittedTypingSourceStatements
import Goose.Lower.Validation.SourceStatementTypingBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

def EmittedSourceStatement (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (stmt : Stmt) : Prop :=
  ∀ {output : Core.TEnv} {start finish : Nat}, Core.tyStmt env scope stmt start = .ok (output, finish) →
  ∀ {initial before : LS} (loop : Option LoopCtx), GeneratedBuilderState before →
  EmittedBuilder (lowerEnv env.mod env.vars results) initial before → EmittedLoopTypes loop before →
  LoopBuilderTargets loop before → before.cur.isSome = true →
  EmittedBuilder (lowerEnv env.mod env.vars results) initial
    (lowerStmt loop stmt (lowerEnv env.mod env.vars results) before).2

def EmittedSourceBlock (env : Core.TEnv) (results : List Ty) (block : Core.Block) : Prop :=
  ∀ {sourcePre : List (VarId × Ty)} {type : Ty} {start finish : Nat},
  Core.tyBlock env sourcePre block start = .ok (type, finish) →
  ∀ {initial before : LS} (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool),
  GeneratedBuilderState before → EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
  EmittedLoopTypes loop before → LoopBuilderTargets loop before →
  (∀ slot value origin, (slot, value, origin) ∈ pre → value < before.vals.size) →
  EmittedBuilder (lowerEnv env.mod env.vars results) initial
    (lowerBlock loop pre want block (lowerEnv env.mod env.vars results) before).2

theorem emitted_source_block_parts {results : List Ty} (scope : ScopeId) (stmts : List Stmt) (value : Option Expr)
    (stmtChildren : ∀ stmt ∈ stmts, ∀ env scope, EmittedSourceStatement env results scope stmt)
    (valueChild : ∀ expr, value = some expr → ∀ env, EmittedSourceExpression env results expr) :
    ∀ env, EmittedSourceBlock env results (.mk scope stmts value) := by
  intro env sourcePre type start finish source initial before loop pre want generated builder loopTypes loopBounds preBounds
  obtain ⟨_, declared, output, statementStart, valueStart, declaration, statements, finalValue⟩ :=
    tyBlock_checked_children source
  have declaredTables := declarePre_tables sourcePre declaration
  have outputTables := tyStmts_tables stmts statements
  have sameDeclared : lowerEnv declared.mod declared.vars results = lowerEnv env.mod env.vars results := by
    rw [declaredTables.1, declaredTables.2.1]
  have sameOutput : lowerEnv output.mod output.vars results = lowerEnv env.mod env.vars results := by
    rw [outputTables.1, outputTables.2.1, sameDeclared]
  have lowered := emitted_checked_generated_lowerBlock builder generated loop loopBounds loopTypes pre preBounds want scope stmts value
    (fun initial started builder generated loopTypes loopBounds => by
      have checked := emitted_checked_source_statements (results := results) stmts statements
        (fun stmt member {childEnv next start finish} source {initial before} loop generated builder loopTypes loopBounds active =>
          ⟨stmtChildren stmt member childEnv scope source loop generated builder loopTypes loopBounds active,
            generated.lowerStmt loop stmt loopBounds rfl⟩)
        loop generated (by simpa only [sameDeclared] using builder) loopTypes loopBounds
      simpa only [sameDeclared] using checked)
    (fun initial started builder generated => by
      refine ⟨?_, generated.lowerBlockValue want value rfl⟩
      cases value with
      | none =>
        cases want
        · exact builder
        · exact builder.emitDef .constUnit (fun _ => ⟨.data .unit, rfl⟩)
            (by intro active operand member; simp [Op.uses] at member)
      | some expr =>
        have checked := valueChild expr rfl output finalValue generated (by simpa only [sameOutput] using builder)
        simpa only [lowerBlockValue, sameOutput] using checked)
  exact lowered.1

end Goose.Lower.Validation
