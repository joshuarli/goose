import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsCommon
import Goose.Lower.Validation.SourceStatementTypingTransfers

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
  {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId}
  {loop : Option LoopCtx} {scope : ScopeId} {initial : LS} {upper : Prov}

theorem statementOccurrence_let_global {index : VarId} {expression : Expr} {origin : OriginId}
    (variablesEmpty : typingEnv.vars = #[]) :
    GlobalStatementOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
      loop scope (.letS index expression origin) initial upper := by
  intro _ output start finish before after typed
  obtain ⟨localVar, childType, childStart, declared, _⟩ := tyStmt_let_children typed
  have row := (declare_ok _ _ _ _ _ declared).2.1
  rw [variablesEmpty] at row
  simp at row

theorem statementOccurrence_rebind_global {index : VarId} {expression : Expr} {origin : OriginId}
    (variablesEmpty : typingEnv.vars = #[]) :
    GlobalStatementOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
      loop scope (.rebind index expression origin) initial upper := by
  intro _ output start finish before after typed
  obtain ⟨localVar, childType, row, _⟩ := tyStmt_rebind_children typed
  rw [variablesEmpty] at row
  simp at row

theorem statementOccurrence_return_global {expression : Expr} {origin : OriginId}
    (inExpression : typingEnv.inExpr = true) :
    GlobalStatementOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
      loop scope (.ret (some expression) origin) initial upper := by
  intro _ output start finish before after typed
  obtain ⟨expected, actual, impl, outside, _⟩ := tyStmt_return_children typed
  rw [inExpression] at outside
  cases outside

theorem statementOccurrence_returnUnit_global {origin : OriginId}
    (inExpression : typingEnv.inExpr = true) :
    GlobalStatementOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
      loop scope (.ret none origin) initial upper := by
  intro _ output start finish before after typed
  have outside := (tyStmt_returnUnit_facts typed).1
  rw [inExpression] at outside
  cases outside

#print axioms statementOccurrence_let_global
#print axioms statementOccurrence_rebind_global
#print axioms statementOccurrence_return_global
#print axioms statementOccurrence_returnUnit_global

end Goose.Lower.Validation.ReplacementContentFlowSource
