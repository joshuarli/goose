import Goose.Lower.Validation.CfgSourceEdgeContracts
import Goose.Lower.Validation.SourceStatementTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem cfg_source_emptyStatements (env : Core.TEnv) (results : List Ty) : CfgSourceStatements env results [] := by
  intro output scope start finish source context
  exact generated_edge_pure _ _ _

theorem cfg_source_consStatements {env : Core.TEnv} {results : List Ty} (stmt : Stmt) (rest : List Stmt)
    (firstChild : CfgSourceStatement env results stmt)
    (restChild : ∀ nextEnv, CfgSourceStatements nextEnv results rest) :
    CfgSourceStatements env results (stmt :: rest) := by
  intro output scope start finish source context
  obtain ⟨middle, next, firstSource, restSource⟩ := tyStmts_cons_children source
  have nextTables := tyStmt_tables stmt firstSource
  have nextLower : lowerEnv middle.mod middle.vars results = lowerEnv env.mod env.vars results := by
    simp only [nextTables.1, nextTables.2.1]
  have restEdges := restChild middle restSource context
  rw [nextLower] at restEdges
  simp only [lowerStmts]
  refine (generated_edge_isLive _ _).bind fun live => ?_
  cases live
  · exact generated_edge_pure _ _ _
  · exact (firstChild firstSource context).bind fun _ => restEdges

theorem cfg_source_block {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (stmts : List Stmt) (value : Option Expr)
    (statementsChild : ∀ nextEnv, CfgSourceStatements nextEnv results stmts)
    (valueChild : ∀ nextEnv expr, value = some expr → CfgSourceExpression nextEnv results expr) :
    CfgSourceBlock env results (.mk scope stmts value) := by
  intro declared ty start finish source context pre want
  obtain ⟨fresh, initializedEnv, finalEnv, statementStart, valueStart, declaration, statementsSource, valueSource⟩ :=
    tyBlock_checked_children source
  have declaredLower := declarePre_lowerEnv declaration results
  have statementLower := tyStmts_lowerEnv statementsSource results
  have finalLower : lowerEnv finalEnv.mod finalEnv.vars results = lowerEnv env.mod env.vars results :=
    statementLower.trans declaredLower
  have statementEdges := statementsChild initializedEnv statementsSource context
  rw [declaredLower] at statementEdges
  have valueEdges : GeneratedEdgeRun (lowerEnv env.mod env.vars results) context (lowerBlockValue want value) := by
    cases value with
    | none => cases want <;> first | exact generated_edge_pure _ _ _ | exact generated_edge_emitDef _ _ _
    | some expr =>
      have child := (valueChild finalEnv expr rfl valueSource).withLoop context
      rw [finalLower] at child
      exact child
  simp only [lowerBlock]
  exact (generated_edge_emitEffect _ _ _).bind fun _ => generated_edge_inScope _ _ scope
    ((generated_edge_initSlots _ _ pre).bind fun _ => statementEdges.bind fun _ => valueEdges.bind fun result =>
      (generated_edge_emitEffect _ _ _).bind fun _ => generated_edge_pure _ _ result)

end Goose.Lower.Validation
