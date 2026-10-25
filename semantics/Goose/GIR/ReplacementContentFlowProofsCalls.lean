import Goose.GIR.ReplacementContentFlowProofsMemory

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem callState_result (m : Module) (states : Array State) (f : Func)
    (state : State) (fn : FnId) (args : List ValueId) (callee : Func) (effects : State)
    (calleeRow : m.funcs[fn]? = some callee) (effectRow : states[fn]? = some effects) :
    (callState m states f state fn args).1 = substitute f state args effects.returned := by
  simp only [callState, calleeRow, effectRow, Id.run_bind, Id.run_pure]

private theorem state_forIn_preserves {α : Type} (values : List α) (predicate : State → Prop)
    (update : α → State → Id (ForInStep State))
    (preserved : ∀ value ∈ values, ∀ state, predicate state → match (update value state).run with
      | .done after | .yield after => predicate after)
    (state : State) (initial : predicate state) : predicate (forIn values state update).run := by
  induction values generalizing state with
  | nil => exact initial
  | cons value values ih =>
      have one := preserved value (by simp) state initial
      cases equation : (update value state).run with
      | done after => simpa [List.forIn_cons, equation] using one
      | yield after =>
          have next : predicate after := by simpa [equation] using one
          simpa [List.forIn_cons, equation] using ih (fun value member => preserved value (List.mem_cons_of_mem _ member)) after next

theorem callState_values (m : Module) (states : Array State) (f : Func)
    (state : State) (fn : FnId) (args : List ValueId) :
    (callState m states f state fn args).2.values = state.values := by
  simp only [callState]
  split
  · split
    · rename_i callee _ effects _
      simp only [Id.run_bind, Id.run_pure]
      apply state_forIn_preserves _ (fun after => after.values = state.values)
      · intro parameter member current known
        by_cases reference : parameter.1.isRefSlice = true
        · simp only [reference, ite_true]
          cases effects.writes[parameter.2]?.getD (.assigned .unknown) with
          | unchanged => exact known
          | assigned roots => exact (write_values _ _ _ _).trans known
        · simpa [reference] using known
      · rfl
    · rfl
  · rfl

theorem callState_returned (m : Module) (states : Array State) (f : Func)
    (state : State) (fn : FnId) (args : List ValueId) :
    (callState m states f state fn args).2.returned = state.returned := by
  simp only [callState]
  split
  · split
    · rename_i callee _ effects _
      simp only [Id.run_bind, Id.run_pure]
      apply state_forIn_preserves _ (fun after => after.returned = state.returned)
      · intro parameter member current known
        by_cases reference : parameter.1.isRefSlice = true
        · simp only [reference, ite_true]
          cases effects.writes[parameter.2]?.getD (.assigned .unknown) with
          | unchanged => exact known
          | assigned roots => exact (write_returned _ _ _ _).trans known
        · simpa [reference] using known
      · rfl
    · rfl
  · rfl

theorem State.MemoryWithin.callState {observer f : Func} {m : Module} {states : Array State}
    {slotUpper contentUpper : Nat → List RootRef} {state : State} {fn : FnId}
    {args : List ValueId} {callee : Func} {effects : State}
    (before : state.MemoryWithin observer slotUpper contentUpper)
    (calleeRow : m.funcs[fn]? = some callee) (effectRow : states[fn]? = some effects)
    (assigned : ∀ type index, (type, index) ∈ callee.params.zipIdx → type.isRefSlice = true →
      ∀ roots, effects.writes[index]?.getD (.assigned .unknown) = .assigned roots →
        let address := (args[index]?).map (flowAt state.values ·) |>.getD .unknown
        address ≠ .unknown ∧ ∀ addresses, address = .known addresses →
          (∀ slot, Atom.local slot ∈ addresses →
            (substitute f state args roots).NormalizedWithin observer (slotUpper slot)) ∧
          (∀ formal, Atom.param formal ∈ addresses →
            (substitute f state args roots).NormalizedWithin observer (contentUpper formal))) :
    (callState m states f state fn args).2.MemoryWithin observer slotUpper contentUpper := by
  simp only [ReplacementContentFlow.Model.callState, calleeRow, effectRow, Id.run_bind, Id.run_pure]
  apply state_forIn_preserves _ (fun current => current.MemoryWithin observer slotUpper contentUpper)
  · intro parameter member current known
    by_cases reference : parameter.1.isRefSlice = true
    · simp only [reference, ite_true]
      cases writeRow : effects.writes[parameter.2]?.getD (.assigned .unknown) with
      | unchanged => exact known
      | assigned roots =>
          have admissible := assigned parameter.1 parameter.2 (by simpa using member) reference roots writeRow
          exact known.write_ready admissible.1 admissible.2
    · simpa [reference] using known
  · exact before.touch _

#print axioms callState_result
#print axioms callState_values
#print axioms callState_returned
#print axioms State.MemoryWithin.callState

end Goose.GIR.ReplacementContentFlow.Model
