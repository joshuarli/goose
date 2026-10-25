import Goose.Lower.Validation.SourceReadyBlocksStatements

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem VisibleSlotsReady.declarePre {env output : TEnv} {state : State}
    {pre : List (VarId × Ty)} {scope start finish : Nat}
    (source : declarePre env scope pre start = .ok (output, finish))
    (visible : VisibleSlotsReady env state)
    (initialized : ∀ slot type, (slot, type) ∈ pre → flowAt state.slots slot ≠ .pending) :
    VisibleSlotsReady output state := by
  induction pre generalizing env start with
  | nil =>
    have same : output = env := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    subst output
    exact visible
  | cons entry rest ih =>
    obtain ⟨slot, type⟩ := entry
    obtain ⟨localVar, next, _, _, remaining⟩ := declarePre_cons_children source
    exact ih remaining (visible.declare (initialized slot type (by simp)))
      (by intro s t member; exact initialized s t (by simp [member]))

theorem SourceReadyFrame.lowerBlock {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {typingEnv declared output : TEnv} {scope start statementsStart valueStart : Nat}
    {sourcePre : List (VarId × Ty)} {pre : List (SlotId × ValueId × OriginId)}
    {loop : Option LoopCtx} {want : Bool} {statements : List Stmt} {value : Option Expr}
    (frame : SourceReadyFrame module callees func types state completed)
    (declaration : declarePre { typingEnv with scopes := scope :: typingEnv.scopes } scope sourcePre start =
      .ok (declared, statementsStart))
    (_checked : Core.tyStmts declared scope statements statementsStart = .ok (output, valueStart))
    (visible : VisibleSlotsReady typingEnv state)
    (preCorrespondence : ∀ slot type, (slot, type) ∈ sourcePre →
      ∃ input origin, (slot, input, origin) ∈ pre)
    (bounded : LiveBound before)
    (extension : (Goose.Lower.lowerBlock loop pre want (.mk scope statements value) env before).2.Ext completed)
    (preSlots : ∀ slot input origin, (slot, input, origin) ∈ pre → slot < func.slots.size)
    (preReady : before.cur.isSome = true → ∀ slot input origin, (slot, input, origin) ∈ pre →
      flowAt state.values input ≠ .pending)
    (children :
      let entered := (emitEffect (.enter scope) env before).2
      let pushed := { entered with stack := scope :: entered.stack }
      let initialized := (Goose.Lower.initSlots pre env pushed).2
      (initialized.cur.isSome = true → VisibleSlotsReady declared state) →
      EmitsOnly (ReadyOperands state) initialized (lowerStmts loop statements env initialized).2 ∧
        ((lowerStmts loop statements env initialized).2.cur.isSome = true → VisibleSlotsReady output state))
    (tail :
      let entered := (emitEffect (.enter scope) env before).2
      let pushed := { entered with stack := scope :: entered.stack }
      let initialized := (Goose.Lower.initSlots pre env pushed).2
      let executed := (lowerStmts loop statements env initialized).2
      (executed.cur.isSome = true → VisibleSlotsReady output state) →
      EmitsOnly (ReadyOperands state) executed (lowerBlockValue want value env executed).2 ∧
        (want = true → (lowerBlockValue want value env executed).2.cur.isSome = true →
          flowAt state.values (lowerBlockValue want value env executed).1 ≠ .pending)) :
    (EmitsOnly (ReadyOperands state) before (Goose.Lower.lowerBlock loop pre want (.mk scope statements value) env before).2 ∧
      (want = true → (Goose.Lower.lowerBlock loop pre want (.mk scope statements value) env before).2.cur.isSome = true →
        flowAt state.values (Goose.Lower.lowerBlock loop pre want (.mk scope statements value) env before).1 ≠ .pending)) ∧
      VisibleSlotsReady typingEnv state := by
  let entered := (emitEffect (.enter scope) env before).2
  let pushed := { entered with stack := scope :: entered.stack }
  let initialized := (Goose.Lower.initSlots pre env pushed).2
  let executed := (lowerStmts loop statements env initialized).2
  let evaluated := lowerBlockValue want value env executed
  let left := (emitEffect (.leave scope) env evaluated.2).2
  have enterReady : EmitsOnly (ReadyOperands state) before entered :=
    ready_emitEffect rfl (by intro _ operand member; simp [Inst.uses, Effect.uses] at member)
  have enteredBound : LiveBound entered := liveBound_of_adv (adv_emitEffect (show emitEffect (.enter scope) env before = ((), entered) from rfl)) bounded
  have pushedBound : LiveBound pushed := enteredBound
  have initExtension : initialized.Ext completed := by
    have steps := advB_lowerStmts loop statements env initialized _ _ rfl
    have outputSteps := advB_lowerBlockValue want value env executed _ _ rfl
    have leaveSteps := adv_emitEffect (show emitEffect (.leave scope) env evaluated.2 = ((), left) from rfl)
    have finalExt : left.Ext (Goose.Lower.lowerBlock loop pre want (.mk scope statements value) env before).2 := by
      exact (EmitsOnly.of_blocks (property := ReadyOperands state) rfl).extension
    exact steps.ext.trans (outputSteps.ext.trans (leaveSteps.ext.trans (finalExt.trans extension)))
  have initReady := frame.initSlots (show Goose.Lower.initSlots pre env pushed = ((), initialized) from rfl)
    initExtension pushedBound preSlots (by
      intro live slot input origin member
      exact preReady ((dead_emitEffect (.enter scope)).live_before rfl live) slot input origin member)
  have declaredReady : initialized.cur.isSome = true → VisibleSlotsReady declared state := by
    intro live
    exact visible.declarePre declaration (by
      intro slot type member
      obtain ⟨input, origin, bound⟩ := preCorrespondence slot type member
      exact initReady.2 live slot input origin bound)
  have statementsReady := children declaredReady
  have valueReady := tail statementsReady.2
  have leaveReady : EmitsOnly (ReadyOperands state) evaluated.2 left :=
    ready_emitEffect rfl (by intro _ operand member; simp [Inst.uses, Effect.uses] at member)
  refine ⟨⟨?_, ?_⟩, visible⟩
  · have pushReady : EmitsOnly (ReadyOperands state) entered pushed := .of_blocks rfl
    have allReady := enterReady.trans (pushReady.trans (initReady.1.trans (statementsReady.1.trans
      (valueReady.1.trans leaveReady))))
    exact allReady.trans (.of_blocks rfl)
  · intro wanted live
    exact valueReady.2 wanted ((dead_emitEffect (.leave scope)).live_before rfl live)

#print axioms VisibleSlotsReady.declarePre
#print axioms SourceReadyFrame.lowerBlock

end Goose.Lower.Validation.ReplacementContentFlowSource
