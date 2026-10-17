import Goose.Lower.Validation.SourceReadyOutput

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem ready_assert {state : State} {env : LEnv} {before : LS}
    {loop : Option LoopCtx} {expression : Expr} {origin : OriginId}
    (child : ValueReadyAt state (lowerExpr expression) env before) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.assertS expression origin) env before).2 := by
  let evaluated := lowerExpr expression env before
  cases current : evaluated.2.cur with
  | none =>
    simp only [lowerStmt, bind_run]
    rw [whenLive_none _ _ _ current]
    exact child.1
  | some block =>
    let forked := fork evaluated.1 env evaluated.2
    let failed := { forked.2 with cur := some forked.1.2 }
    let stopped := (emitTerm (.abort .assert (some origin)) env failed).2
    have forkReady := ready_fork (env := env) (before := evaluated.2) child.2
    have failedReady : EmitsOnly (ReadyOperands state) forked.2 failed := .of_blocks rfl
    have stoppedReady : EmitsOnly (ReadyOperands state) failed stopped := ready_emitTerm (env := env) rfl (by
      intro _ operand member
      simp [Inst.uses, Term.uses] at member)
    have resumedReady : EmitsOnly (ReadyOperands state) stopped { stopped with cur := some forked.1.1 } := .of_blocks rfl
    simpa only [lowerStmt, bind_run, whenLive_some _ _ _ current, setCur_run, pure_run,
      evaluated, forked, failed, stopped] using
      child.1.trans (forkReady.trans (failedReady.trans (stoppedReady.trans resumedReady)))

theorem ready_jump (state : State) (env : LEnv) (before : LS) (depth : Nat) (target : BlockId) :
    EmitsOnly (ReadyOperands state) before ((do
      leaveTo depth
      emitTerm (.br target []) : B Unit) env before).2 := by
  have left := ready_leaveTo state depth env before
  have branch : EmitsOnly (ReadyOperands state) (leaveTo depth env before).2
      (emitTerm (.br target []) env (leaveTo depth env before).2).2 := ready_emitTerm (env := env) rfl (by
    intro _ operand member
    simp [Inst.uses, Term.uses] at member)
  exact left.trans branch

theorem ready_break {state : State} {env : LEnv} {before : LS}
    {loop : Option LoopCtx} {origin : OriginId} :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.brk origin) env before).2 := by
  cases loop with
  | none => exact .refl _ _
  | some context => exact ready_jump state env before context.depth context.breakTo

theorem SourceReadyFrame.continueNext {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {depth : Nat} {header : BlockId} {integerType : IntTy} {index : ValueId}
    (frame : SourceReadyFrame module callees func types state completed)
    (extension : ((do
      leaveTo depth
      let next ← Lower.emitDef (.next integerType index)
      emitTerm (.br header [next]) : B Unit) env before).2.Ext completed)
    (allocated : ((do
      leaveTo depth
      let next ← Lower.emitDef (.next integerType index)
      emitTerm (.br header [next]) : B Unit) env before).2.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before)
    (available : before.cur.isSome = true → flowAt state.values index ≠ .pending) :
    EmitsOnly (ReadyOperands state) before ((do
      leaveTo depth
      let next ← Lower.emitDef (.next integerType index)
      emitTerm (.br header [next]) : B Unit) env before).2 := by
  let left := (leaveTo depth env before).2
  let incremented := Lower.emitDef (.next integerType index) env left
  let branched := (emitTerm (.br header [incremented.1]) env incremented.2).2
  have branchAdvance : incremented.2.Adv branched := adv_emitTerm rfl
  have nextReady := frame.emitDef (show Lower.emitDef (.next integerType index) env left = incremented from rfl)
    (branchAdvance.ext.trans extension) (Nat.le_trans branchAdvance.vals allocated)
    (liveBound_of_advB (advB_leaveTo depth) env before bounded) (by
      intro live operand member
      have same : operand = index := by simpa [Op.uses] using member
      subst operand
      exact available ((dead_ready_leaveTo depth).live_before rfl live))
    (by intro _ value impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
  have branchReady : EmitsOnly (ReadyOperands state) incremented.2 branched := ready_emitTerm (env := env) rfl (by
    intro live operand member
    have same : operand = incremented.1 := by simpa [Inst.uses, Term.uses] using member
    subst operand
    exact nextReady.2 live)
  exact (ready_leaveTo state depth env before).trans (nextReady.1.trans branchReady)

theorem SourceReadyFrame.continue {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {loop : Option LoopCtx} {origin : OriginId}
    (frame : SourceReadyFrame module callees func types state completed)
    (extension : (lowerStmt loop (.cont origin) env before).2.Ext completed)
    (allocated : (lowerStmt loop (.cont origin) env before).2.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before)
    (available : ∀ context, loop = some context → ∀ header integerType index,
      context.cont = .next header integerType index → before.cur.isSome = true →
        flowAt state.values index ≠ .pending) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.cont origin) env before).2 := by
  cases loop with
  | none => exact .refl _ _
  | some context =>
    cases action : context.cont with
    | jump header =>
      simpa only [lowerStmt, action] using ready_jump state env before context.depth header
    | next header integerType index =>
      have actualExtension := extension
      have actualAllocated := allocated
      simp only [lowerStmt, action] at actualExtension actualAllocated ⊢
      exact frame.continueNext actualExtension actualAllocated bounded (available context rfl _ _ _ action)

#print axioms ready_assert
#print axioms ready_jump
#print axioms ready_break
#print axioms SourceReadyFrame.continueNext
#print axioms SourceReadyFrame.continue

end Goose.Lower.Validation.ReplacementContentFlowSource
