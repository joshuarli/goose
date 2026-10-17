import Goose.Lower.Validation.SourceReadyTypedStatementsPrint

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem ready_effect_current (effect : Effect) (env : LEnv) (before : LS) :
    (emitEffect effect env before).2.cur = before.cur := by
  cases current : before.cur with
  | none => rw [emitEffect_none _ _ current]; exact current
  | some block => rw [emitEffect_run _ _ current]; exact current

theorem ready_initSlots_current (pre : List (SlotId × ValueId × OriginId)) (env : LEnv) (before : LS) :
    (Lower.initSlots pre env before).2.cur = before.cur := by
  induction pre generalizing before with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨slot, value, origin⟩ := entry
    exact (ih _).trans (ready_effect_current _ _ _)

theorem SourceReadyFrame.blockPreSlots {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {loop : Option LoopCtx} {pre : List (SlotId × ValueId × OriginId)} {want : Bool} {body : Core.Block}
    (frame : SourceReadyFrame module callees func types state completed)
    (extension : (Lower.lowerBlock loop pre want body env before).2.Ext completed)
    (bounded : LiveBound before) (live : before.cur.isSome = true)
    (slots : ∀ slot value origin, (slot, value, origin) ∈ pre → slot < func.slots.size)
    (values : ∀ slot value origin, (slot, value, origin) ∈ pre → flowAt state.values value ≠ .pending) :
    ∀ slot value origin, (slot, value, origin) ∈ pre → flowAt state.slots slot ≠ .pending := by
  obtain ⟨scope, statements, expression⟩ := body
  let entered := (emitEffect (.enter scope) env before).2
  let pushed := { entered with stack := scope :: entered.stack }
  let initialized := (Lower.initSlots pre env pushed).2
  let executed := (lowerStmts loop statements env initialized).2
  let evaluated := Lower.lowerBlockValue want expression env executed
  let left := (emitEffect (.leave scope) env evaluated.2).2
  have enteredBound : LiveBound entered := liveBound_of_advB (advB_emitEffect (.enter scope)) env before bounded
  have pushedBound : LiveBound pushed := enteredBound
  have initExtension : initialized.Ext completed := by
    have statementsAdvance : initialized.Adv executed := advB_lowerStmts loop statements env initialized _ _ rfl
    have valueAdvance : executed.Adv evaluated.2 := advB_lowerBlockValue want expression env executed _ _ rfl
    have leaveAdvance : evaluated.2.Adv left := adv_emitEffect rfl
    have finalExt : left.Ext (Lower.lowerBlock loop pre want (.mk scope statements expression) env before).2 :=
      (EmitsOnly.of_blocks (property := ReadyOperands state) rfl).extension
    exact statementsAdvance.ext.trans (valueAdvance.ext.trans (leaveAdvance.ext.trans (finalExt.trans extension)))
  have initializedReady := frame.initSlots (show Lower.initSlots pre env pushed = ((), initialized) from rfl)
    initExtension pushedBound slots (fun _ => values)
  have initLive : initialized.cur.isSome = true := by
    rw [show initialized.cur = pushed.cur from ready_initSlots_current pre env pushed]
    simpa only [pushed, entered, ready_effect_current] using live
  exact initializedReady.2 initLive

end Goose.Lower.Validation.ReplacementContentFlowSource
