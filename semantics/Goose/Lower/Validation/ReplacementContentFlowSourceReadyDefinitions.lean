import Goose.Lower.Validation.ReplacementContentFlowSourceReadyReads

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem result_ready_of_operands {func : Func} {types : Array (Option VTy)} {state : State}
    {value : ValueId} {operation : Op}
    (operands : ∀ operand ∈ operation.uses, flowAt state.values operand ≠ .pending)
    (loads : ∀ address, operation = .load address → content func state (flowAt state.values address) ≠ .pending)
    (calls : ∀ fn args origin, operation ≠ .call fn args origin) :
    result func types state value operation ≠ .pending := by
  unfold result
  split
  · simp
  · cases operation <;> simp_all [Op.uses]

theorem call_result_touchValues (module : GIR.Module) (callees : Array State) (func : Func)
    (types : Array (Option VTy)) (state : State) (accesses : List ValueId) (fn : FnId) (args : List ValueId) :
    (callState module callees func (touchValues types state accesses) fn args).1 =
      (callState module callees func state fn args).1 := by
  cases calleeRow : module.funcs[fn]? with
  | none => simp [callState, calleeRow]
  | some callee =>
    cases effectRow : callees[fn]? with
    | none => simp [callState, calleeRow, effectRow]
    | some effects =>
      rw [callState_result _ _ _ _ _ _ _ _ calleeRow effectRow,
        callState_result _ _ _ _ _ _ _ _ calleeRow effectRow]
      rfl

theorem round_definition_ready {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {value : ValueId} {operation : Op}
    (fixed : round module callees func types state = state)
    {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    (instructionMember : Inst.def value operation ∈ block.insts)
    (bounded : value < state.values.size)
    (operands : ∀ operand ∈ operation.uses, flowAt state.values operand ≠ .pending)
    (loads : ∀ address, operation = .load address → content func state (flowAt state.values address) ≠ .pending)
    (calls : ∀ fn args origin, operation = .call fn args origin →
      (callState module callees func state fn args).1 ≠ .pending) :
    flowAt state.values value ≠ .pending := by
  apply fixed_step_def_value_ready
    (round_fixed_step module callees func types state fixed block blockMember _ instructionMember) bounded
  cases operation with
  | call fn args origin =>
    change (if valRefLike types value then
      (callState module callees func (touchValues types state (accessOperands (.def value (.call fn args origin)))) fn args).1
      else .known []) ≠ .pending
    rw [call_result_touchValues]
    split
    · exact calls fn args origin rfl
    · simp
  | load address =>
    exact result_ready_of_operands operands loads (by intro fn args origin impossible; cases impossible)
  | _ =>
    exact result_ready_of_operands operands loads (by intro fn args origin impossible; cases impossible)

#print axioms result_ready_of_operands
#print axioms round_definition_ready

end Goose.Lower.Validation.ReplacementContentFlowSource
