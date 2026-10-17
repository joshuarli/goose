import Goose.GIR.ReplacementContentFlowProofsScopedContentMemory

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

private theorem scoped_memory_forIn {α : Type} (values : List α) (predicate : State → Prop)
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
          simpa [List.forIn_cons, equation] using ih
            (fun value member => preserved value (List.mem_cons_of_mem _ member)) after next

theorem State.ScopedMemoryWithin.callState {module : Module} {states : Array State}
    {func callee : Func} {state effects : State} {function : FnId} {arguments : List ValueId}
    {slots contents : Nat → Prop} {predicate : Atom → Prop}
    (before : state.ScopedMemoryWithin slots contents predicate)
    (calleeAt : module.funcs[function]? = some callee)
    (effectsAt : states[function]? = some effects)
    (assigned : ∀ type index, (type, index) ∈ callee.params.zipIdx → type.isRefSlice = true →
      ∀ roots, effects.writes[index]?.getD (.assigned .unknown) = .assigned roots →
        let address := (arguments[index]?).map (flowAt state.values ·) |>.getD .unknown
        address ≠ .unknown ∧ ∀ addresses, address = .known addresses →
          (∀ slot, slots slot → Atom.local slot ∈ addresses →
            (substitute func state arguments roots).AtomsWithin predicate) ∧
          (∀ index, contents index → Atom.param index ∈ addresses →
            (substitute func state arguments roots).AtomsWithin predicate)) :
    (Model.callState module states func state function arguments).2.ScopedMemoryWithin slots contents predicate := by
  simp only [Model.callState, calleeAt, effectsAt, Id.run_bind, Id.run_pure]
  apply scoped_memory_forIn _ (fun current => current.ScopedMemoryWithin slots contents predicate)
  · intro parameter member current bounded
    by_cases reference : parameter.1.isRefSlice = true
    · simp only [reference, ite_true]
      cases writeAt : effects.writes[parameter.2]?.getD (.assigned .unknown) with
      | unchanged => exact bounded
      | assigned roots =>
          have safe := assigned parameter.1 parameter.2 member reference roots writeAt
          exact write_scoped_memory bounded safe.1
            (fun addresses same => (safe.2 addresses same).1)
            (fun addresses same => (safe.2 addresses same).2)
    · simpa [reference] using bounded
  · exact ⟨before.slots, before.contents⟩

theorem start_scoped_memory {func : Func} {types : Array (Option VTy)}
    {slots contents : Nat → Prop} {predicate : Atom → Prop}
    (bounded : ∀ slot, slots slot → slot < func.slots.size)
    (formals : ∀ index, contents index →
      (flowAt (start func types).contents index).AtomsWithin predicate) :
    (start func types).ScopedMemoryWithin slots contents predicate := by
  constructor
  · intro slot selected
    rw [congrArg State.slots (start_components func types)]
    simp only [flowAt, Array.getElem?_replicate, bounded slot selected, ↓reduceIte,
      Option.getD_some, Roots.AtomsWithin]
  · exact formals

#print axioms State.ScopedMemoryWithin.callState
#print axioms start_scoped_memory

end Goose.GIR.ReplacementContentFlow.Model
