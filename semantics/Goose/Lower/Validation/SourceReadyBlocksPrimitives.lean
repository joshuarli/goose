import Goose.Lower.Validation.ReplacementContentFlowSourceReadyStatements
import Goose.Lower.Validation.ReplacementControl

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem ready_inScope {state : State} {env : LEnv} {before : LS} {scope : ScopeId}
    {action : B α}
    (child : EmitsOnly (ReadyOperands state) { before with stack := scope :: before.stack }
      (action env { before with stack := scope :: before.stack }).2) :
    EmitsOnly (ReadyOperands state) before (inScope scope action env before).2 := by
  change EmitsOnly (ReadyOperands state) before
    { (action env { before with stack := scope :: before.stack }).2 with
      stack := (action env { before with stack := scope :: before.stack }).2.stack.drop 1 }
  have pushed : EmitsOnly (ReadyOperands state) before { before with stack := scope :: before.stack } := .of_blocks rfl
  apply pushed.trans
  exact child.trans (.of_blocks rfl)

theorem SourceReadyFrame.initSlots {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before after : LS}
    {env : LEnv} {pre : List (SlotId × ValueId × OriginId)}
    (frame : SourceReadyFrame module callees func types state completed)
    (run : initSlots pre env before = ((), after))
    (extension : after.Ext completed) (bounded : LiveBound before)
    (slots : ∀ slot value origin, (slot, value, origin) ∈ pre → slot < func.slots.size)
    (values : before.cur.isSome = true → ∀ slot value origin, (slot, value, origin) ∈ pre →
      flowAt state.values value ≠ .pending) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → ∀ slot value origin, (slot, value, origin) ∈ pre →
        flowAt state.slots slot ≠ .pending) := by
  induction pre generalizing before with
  | nil =>
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact ⟨.refl _ _, by simp⟩
  | cons entry rest ih =>
    obtain ⟨slot, value, origin⟩ := entry
    obtain ⟨_, middle, firstRun, restRun⟩ := bind_eq.mp run
    have tail := advB_initSlots rest env middle () after restRun
    have first := ready_emitEffect firstRun (by
      intro live operand member
      have same : operand = value := by simpa [Inst.uses, Effect.uses] using member
      subst operand
      exact values live slot value origin (by simp))
    have remaining := ih restRun (liveBound_of_adv (adv_emitEffect firstRun) bounded)
      (by intro s v o member; exact slots s v o (by simp [member]))
      (by
        intro live s v o member
        exact values ((dead_emitEffect _).live_before firstRun live) s v o (by simp [member]))
    refine ⟨first.trans remaining.1, ?_⟩
    intro live s v o member
    rcases List.mem_cons.mp member with same | later
    · cases same
      have middleLive := (dead_initSlots rest).live_before restRun live
      have initialLive := (dead_emitEffect _).live_before firstRun middleLive
      exact (frame.slotInit firstRun (tail.ext.trans extension) bounded initialLive
        (slots slot value origin (by simp)) (values initialLive slot value origin (by simp))).2
    · exact remaining.2 live s v o later

#print axioms ready_inScope
#print axioms SourceReadyFrame.initSlots

end Goose.Lower.Validation.ReplacementContentFlowSource
