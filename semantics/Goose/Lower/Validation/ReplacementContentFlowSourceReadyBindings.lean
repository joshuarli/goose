import Goose.Lower.Validation.ReplacementContentFlowSourceReadyEmit

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem VisibleSlotsReady.declare {env : TEnv} {state : State} {varId : VarId}
    (before : VisibleSlotsReady env state) (available : flowAt state.slots varId ≠ .pending) :
    VisibleSlotsReady { env with visible := varId :: env.visible } state := by
  intro selectedVar member localVar row reference
  rcases List.mem_cons.mp member with same | previous
  · subst selectedVar
    exact available
  · exact before selectedVar previous localVar row reference

theorem SourceReadyFrame.slotInit {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before after : LS}
    {env : LEnv} {slot : SlotId} {value : ValueId} {origin : Option OriginId}
    (frame : SourceReadyFrame module callees func types state completed)
    (run : emitEffect (.slotInit slot value origin) env before = ((), after))
    (extension : after.Ext completed) (bounded : LiveBound before)
    (live : before.cur.isSome = true)
    (slotBound : slot < func.slots.size) (available : flowAt state.values value ≠ .pending) :
    EmitsOnly (ReadyOperands state) before after ∧ flowAt state.slots slot ≠ .pending := by
  have emitted := emitsOnly_emitEffect (.slotInit slot value origin)
    (show ReadyOperands state (.eff (.slotInit slot value origin)) from by
      unfold ReadyOperands
      constructor
      · intro selected member
        have same : selected = value := by simpa [Inst.uses, Effect.uses] using member
        subst selected
        exact available
      · simp [loadedResults]) env before () after run
  refine ⟨emitted, ?_⟩
  cases current : before.cur with
  | none => simp [current] at live
  | some index =>
    have member : Inst.eff (.slotInit slot value origin) ∈ after.insts := by
      rw [emitEffect_run _ _ current] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      let body := before.blocks[index]'(bounded index current)
      have row : before.blocks[index]? = some body := by simp [body]
      have afterRow : (before.blocks.modify index (fun blk => { blk with insts := blk.insts.push (.eff (.slotInit slot value origin)) }))[index]? =
          some { body with insts := body.insts.push (.eff (.slotInit slot value origin)) } := by
        simp [Array.getElem?_modify, row]
      exact List.mem_flatMap.mpr ⟨_, Array.mem_toList_iff.mpr (Array.mem_of_getElem? afterRow), by simp⟩
    exact fixed_slotInit_ready (frame.fixed_instruction extension member)
      (by simpa only [frame.shape.slots] using slotBound) available

theorem SourceReadyFrame.declare {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before after : LS}
    {env : LEnv} {typingEnv : TEnv} {slot : SlotId} {value : ValueId} {origin : Option OriginId}
    (frame : SourceReadyFrame module callees func types state completed)
    (run : emitEffect (.slotInit slot value origin) env before = ((), after))
    (extension : after.Ext completed) (bounded : LiveBound before)
    (live : before.cur.isSome = true)
    (slotBound : slot < func.slots.size) (available : flowAt state.values value ≠ .pending)
    (visible : VisibleSlotsReady typingEnv state) :
    EmitsOnly (ReadyOperands state) before after ∧
      VisibleSlotsReady { typingEnv with visible := slot :: typingEnv.visible } state := by
  obtain ⟨emitted, initialized⟩ := frame.slotInit run extension bounded live slotBound available
  exact ⟨emitted, visible.declare initialized⟩

#print axioms VisibleSlotsReady.declare
#print axioms SourceReadyFrame.slotInit
#print axioms SourceReadyFrame.declare

end Goose.Lower.Validation.ReplacementContentFlowSource
