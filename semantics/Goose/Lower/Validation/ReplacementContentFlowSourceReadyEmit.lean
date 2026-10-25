import Goose.Lower.Validation.ReplacementContentFlowSourceReadyBuilder
import Goose.Lower.Validation.CfgFrontier

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.emitDef {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before after : LS}
    {env : LEnv} {value : ValueId} {operation : Op}
    (frame : SourceReadyFrame module callees func types state completed)
    (run : Lower.emitDef operation env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before)
    (operands : before.cur.isSome = true → ∀ operand ∈ operation.uses, flowAt state.values operand ≠ .pending)
    (loads : before.cur.isSome = true → ∀ address, operation = .load address →
      valRefLike types before.vals.size = true → content func state (flowAt state.values address) ≠ .pending)
    (calls : before.cur.isSome = true → ∀ fn args origin, operation = .call fn args origin →
      valRefLike types before.vals.size = true → (callState module callees func state fn args).1 ≠ .pending) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  cases current : before.cur with
  | none =>
    rw [emitDef_none _ _ current] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact ⟨.refl _ _, by simp [current]⟩
  | some index =>
    have live : before.cur.isSome = true := by simp [current]
    have emitRun := run
    rw [emitDef_run _ _ current] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    let body := before.blocks[index]'(bounded index current)
    have row : before.blocks[index]? = some body := by simp [body]
    have afterRow : (before.blocks.modify index (fun blk => { blk with insts := blk.insts.push (.def before.vals.size operation) }))[index]? =
        some { body with insts := body.insts.push (.def before.vals.size operation) } := by
      simp [Array.getElem?_modify, row]
    have member : Inst.def before.vals.size operation ∈
        ({ before with
          vals := before.vals.push (some (((operation.resultTy (tyEnv env before)).toOption).getD (.data .unit)))
          blocks := before.blocks.modify index (fun blk => { blk with insts := blk.insts.push (.def before.vals.size operation) }) } : LS).insts := by
      apply List.mem_flatMap.mpr
      refine ⟨_, Array.mem_toList_iff.mpr (Array.mem_of_getElem? afterRow), ?_⟩
      simp
    have fixed := frame.fixed_instruction extension member
    have valueBound : before.vals.size < state.values.size := by
      rw [frame.shape.values, ← frame.values]
      have allocation : before.vals.size + 1 ≤ completed.vals.size := by simpa using allocated
      omega
    have resultReady : flowAt state.values before.vals.size ≠ .pending := by
      apply fixed_step_def_value_ready fixed valueBound
      cases operation with
      | call fn args origin =>
        change (if valRefLike types before.vals.size then
          (callState module callees func (touchValues types state (accessOperands (.def before.vals.size (.call fn args origin)))) fn args).1
          else .known []) ≠ .pending
        rw [call_result_touchValues]
        split
        · exact calls live fn args origin rfl ‹valRefLike types before.vals.size = true›
        · simp
      | _ =>
        by_cases reference : valRefLike types before.vals.size = true
        · exact result_ready_of_operands (operands live)
            (fun address same => loads live address same reference)
            (by intro fn args origin impossible; cases impossible)
        · simp [result, reference]
    have ready : ReadyOperands state (.def before.vals.size operation) := by
      unfold ReadyOperands
      constructor
      · exact operands live
      · intro result member
        cases operation with
        | load address =>
          simp only [loadedResults, List.mem_singleton] at member
          subst result
          exact resultReady
        | _ => simp [loadedResults] at member
    have emissions := emitsOnly_emitDef emitRun ready
    exact ⟨emissions, fun _ => resultReady⟩

#print axioms SourceReadyFrame.emitDef

end Goose.Lower.Validation.ReplacementContentFlowSource
