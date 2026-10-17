import Goose.GIR.ReplacementContentFlowProofsCalls
import Goose.GIR.ReplacementContentFlowProofsOrder

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

@[simp] theorem touchValues_values (vt : Array (Option VTy)) (state : State) (values : List ValueId) :
    (touchValues vt state values).values = state.values := rfl

@[simp] theorem touchValues_slots (vt : Array (Option VTy)) (state : State) (values : List ValueId) :
    (touchValues vt state values).slots = state.slots := rfl

@[simp] theorem touchValues_contents (vt : Array (Option VTy)) (state : State) (values : List ValueId) :
    (touchValues vt state values).contents = state.contents := rfl

@[simp] theorem touchValues_writes (vt : Array (Option VTy)) (state : State) (values : List ValueId) :
    (touchValues vt state values).writes = state.writes := rfl

@[simp] theorem touchValues_returned (vt : Array (Option VTy)) (state : State) (values : List ValueId) :
    (touchValues vt state values).returned = state.returned := rfl

theorem result_touchValues (f : Func) (vt : Array (Option VTy)) (state : State)
    (accesses : List ValueId) (value : ValueId) (op : Op) :
    result f vt (touchValues vt state accesses) value op = result f vt state value op := by
  cases op <;> rfl

theorem callState_result_touchValues (module : Module) (states : Array State) (func : Func)
    (types : Array (Option VTy)) (state : State) (accesses args : List ValueId) (fn : FnId) :
    (callState module states func (touchValues types state accesses) fn args).1 =
      (callState module states func state fn args).1 := by
  cases calleeAt : module.funcs[fn]? with
  | none => simp [callState,calleeAt]
  | some callee =>
      cases effectsAt : states[fn]? with
      | none => simp [callState,calleeAt,effectsAt]
      | some effects =>
          rw [callState_result _ _ _ _ _ _ _ _ calleeAt effectsAt,
            callState_result _ _ _ _ _ _ _ _ calleeAt effectsAt]
          rfl

theorem step_def_values (m : Module) (states : Array State) (f : Func)
    (vt : Array (Option VTy)) (state : State) (value : ValueId) (op : Op) :
    (step m states f vt state (.def value op)).values = addFlow state.values value
      (match op with
        | .call fn args _ => if valRefLike vt value then
            (callState m states f (touchValues vt state (accessOperands (.def value op))) fn args).1
            else .known []
        | _ => result f vt state value op) := by
  cases op <;> simp only [step, Id.run_pure, touchValues_values, result_touchValues]
  rw [callState_values,callState_result_touchValues]

theorem step_def_values_within {m : Module} {states : Array State} {f observer : Func}
    {vt : Array (Option VTy)} {state : State} {value : ValueId} {op : Op}
    {upper : Nat → List RootRef} (before : CellsWithin observer upper state.values)
    (produced : (match op with
      | .call fn args _ => if valRefLike vt value then
          (callState m states f (touchValues vt state (accessOperands (.def value op))) fn args).1
          else .known []
      | _ => result f vt state value op).NormalizedWithin observer (upper value)) :
    CellsWithin observer upper (step m states f vt state (.def value op)).values := by
  rw [step_def_values]
  exact before.addFlow produced

theorem Roots.join_ready_right (left right : Roots) (ready : right ≠ .pending) :
    left.join right ≠ .pending := by
  cases left <;> cases right <;> simp_all [Roots.join]

theorem Roots.join_ready_left (left right : Roots) (ready : left ≠ .pending) :
    left.join right ≠ .pending := by
  cases left <;> cases right <;> simp_all [Roots.join]

theorem step_def_value_ready (m : Module) (states : Array State) (f : Func)
    (vt : Array (Option VTy)) (state : State) (value : ValueId) (op : Op)
    (bounded : value < state.values.size)
    (produced : (match op with
      | .call fn args _ => if valRefLike vt value then
          (callState m states f (touchValues vt state (accessOperands (.def value op))) fn args).1
          else .known []
      | _ => result f vt state value op) ≠ .pending) :
    flowAt (step m states f vt state (.def value op)).values value ≠ .pending := by
  rw [step_def_values, flowAt_addFlow]
  simp only [bounded, and_self, ite_true]
  exact Roots.join_ready_right _ _ produced

theorem fixed_step_def_value_ready {m : Module} {states : Array State} {f : Func}
    {vt : Array (Option VTy)} {state : State} {value : ValueId} {op : Op}
    (fixed : step m states f vt state (.def value op) = state)
    (bounded : value < state.values.size)
    (produced : (match op with
      | .call fn args _ => if valRefLike vt value then
          (callState m states f (touchValues vt state (accessOperands (.def value op))) fn args).1
          else .known []
      | _ => result f vt state value op) ≠ .pending) :
    flowAt state.values value ≠ .pending := by
  rw [← fixed]
  exact step_def_value_ready m states f vt state value op bounded produced

theorem fixed_step_def_normalized {m : Module} {states : Array State} {f observer : Func}
    {vt : Array (Option VTy)} {state : State} {value : ValueId} {op : Op}
    {upper : Nat → List RootRef}
    (fixed : step m states f vt state (.def value op) = state)
    (valuesBound : CellsWithin observer upper state.values)
    (bounded : value < state.values.size)
    (produced : (match op with
      | .call fn args _ => if valRefLike vt value then
          (callState m states f (touchValues vt state (accessOperands (.def value op))) fn args).1
          else .known []
      | _ => result f vt state value op) ≠ .pending) :
    ∃ actual, normalize observer (flowAt state.values value) = some actual ∧ actual ⊆ upper value :=
  (valuesBound value bounded).actual (fixed_step_def_value_ready fixed bounded produced)

theorem edge_returned (f : Func) (state : State) (target : BlockId) (args : List ValueId) :
    (edge f state target args).returned = state.returned := by
  unfold edge
  split
  · rfl
  · rename_i block row
    apply List.foldlRecOn (motive := fun (current : State) => current.returned = state.returned)
      (block.params.zip args) _ rfl
    intro current preserved pair member
    exact preserved

theorem step_returned (m : Module) (states : Array State) (f : Func)
    (vt : Array (Option VTy)) (state : State) (inst : Inst) :
    (step m states f vt state inst).returned = match inst with
      | .term (.ret [value] _) => state.returned.join (flowAt state.values value)
      | _ => state.returned := by
  cases inst with
  | «def» value op =>
      cases op <;> simp only [step, Id.run_pure, touchValues_returned]
      rw [callState_returned]
  | eff effect =>
      cases effect <;> simp only [step, Id.run_pure, touchValues_returned]
      split
      · rw [write_returned, touchValues_returned]
      · rfl
  | term term =>
      cases term <;> simp only [step, Id.run_pure, touchValues_returned, edge_returned]
      case ret values origin =>
        cases values with
        | nil => rfl
        | cons value rest => cases rest <;> rfl

#print axioms step_returned
#print axioms step_def_values
#print axioms step_def_values_within
#print axioms fixed_step_def_normalized
#print axioms step_def_value_ready
#print axioms fixed_step_def_value_ready

end Goose.GIR.ReplacementContentFlow.Model
