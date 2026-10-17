import Goose.Lower.Validation.SourceReadyMutationsGenerated
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyLists

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem ready_leaveAll (state : State) (scopes : List ScopeId) (env : LEnv) (before : LS) :
    EmitsOnly (ReadyOperands state) before (leaveAll scopes env before).2 := by
  induction scopes generalizing before with
  | nil => exact .refl _ _
  | cons scope rest ih =>
    have first : EmitsOnly (ReadyOperands state) before (emitEffect (.leave scope) env before).2 := ready_emitEffect rfl (by
      intro _ value member
      simp [Inst.uses, Effect.uses] at member)
    exact first.trans (ih _)

theorem ready_leaveTo (state : State) (depth : Nat) (env : LEnv) (before : LS) :
    EmitsOnly (ReadyOperands state) before (leaveTo depth env before).2 := ready_leaveAll state _ env before

theorem dead_ready_leaveAll (scopes : List ScopeId) : DeadRun (leaveAll scopes) := by
  induction scopes with
  | nil => exact DeadRun.pure ()
  | cons scope rest ih => exact DeadRun.bind (dead_emitEffect (.leave scope)) (fun _ => ih)

theorem dead_ready_leaveTo (depth : Nat) : DeadRun (leaveTo depth) := by
  unfold leaveTo
  exact DeadRun.bind (DeadRun.of_cur_unchanged (fun _ _ => rfl)) (fun _ => dead_ready_leaveAll _)

theorem ready_return_none {state : State} {env : LEnv} {before : LS}
    {loop : Option LoopCtx} {origin : OriginId} :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.ret none origin) env before).2 := by
  have leaving := ready_leaveTo state 0 env before
  have returning : EmitsOnly (ReadyOperands state) (leaveTo 0 env before).2
      (emitTerm (.ret [] (some origin)) env (leaveTo 0 env before).2).2 := ready_emitTerm rfl (by
    intro _ operand member
    simp [Inst.uses, Term.uses] at member)
  exact leaving.trans returning

theorem SourceReadyFrame.return_some {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {loop : Option LoopCtx} {expression : Expr} {origin : OriginId}
    (frame : SourceReadyFrame module callees func types state completed)
    (extension : (lowerStmt loop (.ret (some expression) origin) env before).2.Ext completed)
    (allocated : (lowerStmt loop (.ret (some expression) origin) env before).2.vals.size ≤ completed.vals.size)
    (bounded : LiveBound (lowerExpr expression env before).2)
    (child : ValueReadyAt state (lowerExpr expression) env before) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.ret (some expression) origin) env before).2 := by
  let evaluated := lowerExpr expression env before
  let coerced := Lower.coerceResult evaluated.1 origin env evaluated.2
  let left := (leaveTo 0 env coerced.2).2
  let returned := (emitTerm (.ret [coerced.1] (some origin)) env left).2
  have leaveAdvance : coerced.2.Adv left := advB_leaveTo 0 env coerced.2 _ _ rfl
  have returnAdvance : left.Adv returned := adv_emitTerm rfl
  have coerceReady := frame.coerceResult (show Lower.coerceResult evaluated.1 origin env evaluated.2 = coerced from rfl)
    (leaveAdvance.ext.trans (returnAdvance.ext.trans extension))
    (Nat.le_trans leaveAdvance.vals (Nat.le_trans returnAdvance.vals allocated)) bounded child.2
  have leaving := ready_leaveTo state 0 env coerced.2
  have returning : EmitsOnly (ReadyOperands state) left returned := ready_emitTerm rfl (by
    intro live operand member
    have same : operand = coerced.1 := by simpa [Inst.uses, Term.uses] using member
    subst operand
    exact coerceReady.2 ((dead_ready_leaveTo 0).live_before rfl live))
  exact child.1.trans (coerceReady.1.trans (leaving.trans returning))

theorem ready_print {state : State} {env : LEnv} {before : LS}
    {loop : Option LoopCtx} {arguments : List PrintArg} {origin : OriginId}
    (children : PrintArgumentsReadyAt state arguments env before) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.print arguments origin) env before).2 := by
  let printed := lowerPrintArgs arguments env before
  have effectReady : EmitsOnly (ReadyOperands state) printed.2
      (emitEffect (.print printed.1 (some origin)) env printed.2).2 := ready_emitEffect rfl (by
    intro live operand member
    obtain ⟨part, partMember, use⟩ := List.mem_flatMap.mp member
    cases part with
    | text text => simp [PrintPart.uses] at use
    | val value =>
      have same : operand = value := by simpa [PrintPart.uses] using use
      subst operand
      exact children.2 live value partMember)
  exact children.1.trans effectReady

theorem ready_abort {state : State} {env : LEnv} {before : LS}
    {loop : Option LoopCtx} {kind : String} {origin : OriginId} :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.abort kind origin) env before).2 := by
  exact ready_emitTerm rfl (by intro _ operand member; simp [Inst.uses, Term.uses] at member)

theorem ready_exit {state : State} {env : LEnv} {before : LS}
    {loop : Option LoopCtx} {expression : Expr} {origin : OriginId}
    (child : ValueReadyAt state (lowerExpr expression) env before) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.exit expression origin) env before).2 := by
  let evaluated := lowerExpr expression env before
  have exiting : EmitsOnly (ReadyOperands state) evaluated.2
      (emitTerm (.exit evaluated.1 (some origin)) env evaluated.2).2 := ready_emitTerm rfl (by
    intro live operand member
    have same : operand = evaluated.1 := by simpa [Inst.uses, Term.uses] using member
    subst operand
    exact child.2 live)
  exact child.1.trans exiting

#print axioms ready_leaveAll
#print axioms ready_leaveTo
#print axioms dead_ready_leaveAll
#print axioms dead_ready_leaveTo
#print axioms ready_return_none
#print axioms SourceReadyFrame.return_some
#print axioms ready_print
#print axioms ready_abort
#print axioms ready_exit

end Goose.Lower.Validation.ReplacementContentFlowSource
