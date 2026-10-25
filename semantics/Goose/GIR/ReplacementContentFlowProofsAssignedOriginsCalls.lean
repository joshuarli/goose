import Goose.GIR.ReplacementContentFlowProofsAssignedOriginsSubstitution

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def callWriteStep (func : Func) (before : State) (arguments : List ValueId)
    (effects : State) (state : State) (parameter : Ty × Nat) : State :=
  if parameter.1.isRefSlice then
    match effects.writes[parameter.2]?.getD (.assigned .unknown) with
    | .unchanged => state
    | .assigned roots =>
      write func state ((arguments[parameter.2]?).map (flowAt before.values ·) |>.getD .unknown)
        (substitute func before arguments roots)
  else state

theorem callWriteStep_extends (func : Func) (before : State) (arguments : List ValueId)
    (effects state : State) (parameter : Ty × Nat) :
    state.Extends (callWriteStep func before arguments effects state parameter) := by
  unfold callWriteStep
  split
  · split
    · exact State.Extends.refl _
    · exact write_extends _ _ _ _
  · exact State.Extends.refl _

theorem callState_fold (module : Module) (states : Array State) (func : Func)
    (state : State) (calleeId : FnId) (arguments : List ValueId) (callee : Func) (effects : State)
    (calleeAt : module.funcs[calleeId]? = some callee)
    (effectsAt : states[calleeId]? = some effects) :
    (callState module states func state calleeId arguments).2 =
      callee.params.zipIdx.foldl (callWriteStep func state arguments effects)
        { state with touched := state.touched.join (substitute func state arguments (publicTouches effects.touched)) } := by
  simp only [callState, calleeAt, effectsAt, Id.run_bind, Id.run_pure]
  have loops : ∀ (parameters : List (Ty × Nat)) (current : State),
      (forIn parameters current (fun parameter current => do
        if parameter.1.isRefSlice then
          match effects.writes[parameter.2]?.getD (.assigned .unknown) with
          | .unchanged => pure (.yield current)
          | .assigned roots => pure (.yield (write func current
              ((arguments[parameter.2]?).map (flowAt state.values ·) |>.getD .unknown)
              (substitute func state arguments roots)))
        else pure (.yield current)) : Id State).run =
        parameters.foldl (callWriteStep func state arguments effects) current := by
    intro parameters current
    induction parameters generalizing current with
    | nil => rfl
    | cons parameter parameters ih =>
      simp only [List.forIn_cons, List.foldl_cons, callWriteStep]
      split
      · split <;> exact ih _
      · exact ih _
  exact loops _ _

theorem callWriteStep_assigned_origin (func : Func) (before : State)
    (arguments : List ValueId) (effects state : State) (parameter : Ty × Nat) (index : Nat)
    (safe : ((arguments[parameter.2]?).map (flowAt before.values ·) |>.getD .unknown) ≠ .unknown)
    (bounded : parameter.2 < effects.writes.size)
    (assigned : Write.AssignedAt
      (callWriteStep func before arguments effects state parameter).writes index) :
    Write.AssignedAt state.writes index ∨
      parameter.1.isRefSlice = true ∧ Write.AssignedAt effects.writes parameter.2 ∧
        ∃ atoms, ((arguments[parameter.2]?).map (flowAt before.values ·) |>.getD .unknown) =
          .known atoms ∧ .param index ∈ atoms ∧
          (func.params[index]?).any Ty.isRefSlice = true := by
  unfold callWriteStep at assigned
  split at assigned
  · rename_i reference
    split at assigned
    · exact Or.inl assigned
    · rename_i roots found
      rcases write_assigned_origin func state _ _ index safe assigned with old | fresh
      · exact Or.inl old
      · obtain ⟨atoms, known, member, _, slice⟩ := fresh
        refine Or.inr ⟨reference, ?_, atoms, known, member, slice⟩
        refine ⟨roots, ?_⟩
        simpa only [Array.getElem?_eq_getElem bounded, Option.getD_some] using
          congrArg some found
  · exact Or.inl assigned

theorem callWrites_assigned_origin (func : Func) (before : State)
    (arguments : List ValueId) (effects state : State) (parameters : List (Ty × Nat)) (index : Nat)
    (safe : ∀ parameter ∈ parameters,
      ((arguments[parameter.2]?).map (flowAt before.values ·) |>.getD .unknown) ≠ .unknown)
    (bounded : ∀ parameter ∈ parameters, parameter.2 < effects.writes.size)
    (assigned : Write.AssignedAt
      (parameters.foldl (callWriteStep func before arguments effects) state).writes index) :
    Write.AssignedAt state.writes index ∨
      ∃ parameter ∈ parameters, parameter.1.isRefSlice = true ∧
        Write.AssignedAt effects.writes parameter.2 ∧
        ∃ atoms, ((arguments[parameter.2]?).map (flowAt before.values ·) |>.getD .unknown) =
          .known atoms ∧ .param index ∈ atoms ∧
          (func.params[index]?).any Ty.isRefSlice = true := by
  induction parameters generalizing state with
  | nil => exact Or.inl assigned
  | cons parameter parameters ih =>
    rcases ih (callWriteStep func before arguments effects state parameter)
      (fun p h => safe p (List.mem_cons_of_mem _ h))
      (fun p h => bounded p (List.mem_cons_of_mem _ h)) assigned with first | later
    · rcases callWriteStep_assigned_origin func before arguments effects state parameter index
        (safe parameter (by simp)) (bounded parameter (by simp)) first with old | fresh
      · exact Or.inl old
      · exact Or.inr ⟨parameter, by simp, fresh⟩
    · obtain ⟨p, member, rest⟩ := later
      exact Or.inr ⟨p, List.mem_cons_of_mem _ member, rest⟩

#print axioms callState_fold

end Goose.GIR.ReplacementContentFlow.Model
