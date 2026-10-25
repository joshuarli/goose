import Goose.GIR.ReplacementContentFlowProofsAssignedOriginsCalls

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem callWrites_parameter_ready (func : Func) (before : State)
    (arguments : List ValueId) (effects state : State) (parameters : List (Ty × Nat))
    (parameter : Ty × Nat) (index : Nat) (roots : Roots) (addresses : List Atom)
    (member : parameter ∈ parameters) (slice : parameter.1.isRefSlice = true)
    (written : effects.writes[parameter.2]? = some (.assigned roots))
    (address : ((arguments[parameter.2]?).map (flowAt before.values ·) |>.getD .unknown) =
      .known addresses) (target : .param index ∈ addresses)
    (bounded : index < state.writes.size)
    (reference : (func.params[index]?).any Ty.isRefSlice = true)
    (ready : substitute func before arguments roots ≠ .pending) :
    Write.ReadyAt
      (parameters.foldl (callWriteStep func before arguments effects) state).writes index := by
  induction parameters generalizing state with
  | nil => simp at member
  | cons first parameters ih =>
    rcases List.mem_cons.mp member with same | later
    · subst first
      have selected : Write.ReadyAt
          (callWriteStep func before arguments effects state parameter).writes index := by
        simp only [callWriteStep, slice, ite_true, written, Option.getD_some, address]
        exact write_known_parameter_ready func state addresses _ index target bounded reference ready
      exact selected.extends
        (state_foldl_extends parameters _
          (fun current p => callWriteStep_extends func before arguments effects current p) _).writes
    · have growth := (callWriteStep_extends func before arguments effects state first).writes
      exact ih _ later (by simpa [← growth.size] using bounded)

theorem callState_parameter_ready (module : Module) (states : Array State) (func : Func)
    (state : State) (calleeId : FnId) (arguments : List ValueId) (callee : Func) (effects : State)
    (calleeAt : module.funcs[calleeId]? = some callee)
    (effectsAt : states[calleeId]? = some effects)
    (parameter : Ty × Nat) (index : Nat) (roots : Roots) (addresses : List Atom)
    (member : parameter ∈ callee.params.zipIdx) (slice : parameter.1.isRefSlice = true)
    (written : effects.writes[parameter.2]? = some (.assigned roots))
    (address : ((arguments[parameter.2]?).map (flowAt state.values ·) |>.getD .unknown) =
      .known addresses) (target : .param index ∈ addresses)
    (bounded : index < state.writes.size)
    (reference : (func.params[index]?).any Ty.isRefSlice = true)
    (ready : substitute func state arguments roots ≠ .pending) :
    Write.ReadyAt (callState module states func state calleeId arguments).2.writes index := by
  rw [callState_fold module states func state calleeId arguments callee effects calleeAt effectsAt]
  exact callWrites_parameter_ready func state arguments effects _ callee.params.zipIdx
    parameter index roots addresses member slice written address target bounded reference ready

#print axioms callWrites_parameter_ready
#print axioms callState_parameter_ready

end Goose.GIR.ReplacementContentFlow.Model
