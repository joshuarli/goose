import Goose.Lower.Validation.SourceGlobalControlLeaves
import Goose.Lower.Validation.SourceStatementTypingControl

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
  {target : Core.Eff} {scopeCount : Nat} {loop : Option LoopCtx} {scope : ScopeId} {initial : LS} {upper : Prov}

theorem globalStatementReplay_let {slot : VarId} {expression : Expr} {origin : OriginId}
    (variables : typingEnv.vars = #[]) :
    GlobalStatementReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope
      (.letS slot expression origin) initial upper := by
  intro output start finish before after typed
  obtain ⟨localVar, type, childStart, declared, _⟩ := tyStmt_let_children typed
  have row := (declare_ok _ _ _ _ _ declared).2.1
  simp [variables] at row

theorem globalStatementReplay_rebind {slot : VarId} {expression : Expr} {origin : OriginId}
    (variables : typingEnv.vars = #[]) :
    GlobalStatementReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope
      (.rebind slot expression origin) initial upper := by
  intro output start finish before after typed
  obtain ⟨localVar, type, row, _⟩ := tyStmt_rebind_children typed
  simp [variables] at row

theorem globalStatementReplay_forRange {slot : VarId} {low high : Expr} {body : Core.Block} {origin : OriginId}
    (variables : typingEnv.vars = #[]) :
    GlobalStatementReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope
      (.forRange slot low high body origin) initial upper := by
  intro output start finish before after typed
  obtain ⟨localVar, integer, childStart, lowFinish, highFinish, bodyType, declared, _⟩ := tyStmt_forRange_children typed
  have row := (declare_ok _ _ _ _ _ declared).2.1
  simp [variables] at row

theorem globalStatementReplay_forEach {slot : VarId} {index : Option VarId} {view : View}
    {byRef : Bool} {body : Core.Block} {origin : OriginId}
    (variables : typingEnv.vars = #[]) :
    GlobalStatementReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope
      (.forEach slot index view byRef body origin) initial upper := by
  intro output start finish before after typed
  obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType, declared, _⟩ := tyStmt_forEach_children typed
  have row := (declare_ok _ _ _ _ _ declared).2.1
  simp [variables] at row

theorem globalStatementReplay_return {value : Option Expr} {origin : OriginId}
    (inside : typingEnv.inExpr = true) :
    GlobalStatementReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope
      (.ret value origin) initial upper := by
  intro output start finish before after typed
  cases value with
  | none =>
    have outside := (tyStmt_returnUnit_facts typed).1
    rw [inside] at outside
    cases outside
  | some expression =>
    obtain ⟨expected, actual, impl, outside, _⟩ := tyStmt_return_children typed
    rw [inside] at outside
    cases outside

end Goose.Lower.Validation.SummaryPreservation
