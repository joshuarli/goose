import Goose.GIR.ReplacementContentFlowProofsTransfer
import Goose.GIR.ReplacementContentFlowProofsSupportStart

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def CellsWithin (observer : Func) (upper : Nat → List RootRef) (values : Array Roots) : Prop :=
  ∀ index, index < values.size → (flowAt values index).NormalizedWithin observer (upper index)

def ContentCellsWithin (observer : Func) (upper : Nat → List RootRef) (values : Array Roots) : Prop :=
  ∀ index, index < values.size →
    (observer.roots.contents.find? (·.1 == index)).isSome = true →
      (flowAt values index).NormalizedWithin observer (upper index)

def Write.NormalizedWithin (observer : Func) (upper : List RootRef) : Write → Prop
  | .unchanged => True
  | .assigned roots => roots.NormalizedWithin observer upper

def WritesWithin (observer : Func) (upper : Nat → List RootRef) (values : Array Write) : Prop :=
  ∀ index, index < values.size →
    (values[index]?.getD (.assigned .unknown)).NormalizedWithin observer (upper index)

structure State.MemoryWithin (observer : Func) (slotUpper contentUpper : Nat → List RootRef)
    (state : State) : Prop where
  slots : CellsWithin observer slotUpper state.slots
  contents : ContentCellsWithin observer contentUpper state.contents
  writes : WritesWithin observer contentUpper state.writes

theorem Write.NormalizedWithin.join {observer : Func} {upper : List RootRef} {left right : Write}
    (leftBound : left.NormalizedWithin observer upper)
    (rightBound : right.NormalizedWithin observer upper) :
    (left.join right).NormalizedWithin observer upper := by
  cases left <;> cases right <;> simp_all only [Write.NormalizedWithin, Write.join]
  exact leftBound.join rightBound

theorem flowAt_addFlow (values : Array Roots) (index cell : Nat) (roots : Roots) :
    flowAt (addFlow values index roots) cell =
      if cell = index ∧ index < values.size then (flowAt values index).join roots
      else flowAt values cell := by
  by_cases same : cell = index
  · subst cell
    by_cases bounded : index < values.size
    · simp [ReplacementContentFlow.Model.addFlow, flowAt, bounded]
    · simp [ReplacementContentFlow.Model.addFlow, flowAt, bounded]
  · have different : index ≠ cell := Ne.symm same
    simp [ReplacementContentFlow.Model.addFlow, flowAt, same, different]

theorem CellsWithin.addFlow {observer : Func} {upper : Nat → List RootRef}
    {values : Array Roots} {index : Nat} {roots : Roots}
    (before : CellsWithin observer upper values)
    (added : roots.NormalizedWithin observer (upper index)) :
    CellsWithin observer upper (addFlow values index roots) := by
  intro cell bounded
  have originalBound : cell < values.size := by simpa [ReplacementContentFlow.Model.addFlow] using bounded
  rw [flowAt_addFlow]
  split
  · rename_i updated
    rcases updated with ⟨same, valid⟩
    subst cell
    exact (before index originalBound).join added
  · exact before cell originalBound

theorem ContentCellsWithin.addFlow {observer : Func} {upper : Nat → List RootRef}
    {values : Array Roots} {index : Nat} {roots : Roots}
    (before : ContentCellsWithin observer upper values)
    (added : roots.NormalizedWithin observer (upper index)) :
    ContentCellsWithin observer upper (addFlow values index roots) := by
  intro cell bounded observed
  have originalBound : cell < values.size := by
    simpa [ReplacementContentFlow.Model.addFlow] using bounded
  rw [flowAt_addFlow]
  split
  · rename_i updated
    have same := updated.1
    subst cell
    exact (before index originalBound observed).join added
  · exact before cell originalBound observed

theorem WritesWithin.assign {observer : Func} {upper : Nat → List RootRef}
    {values : Array Write} {index : Nat} {roots : Roots}
    (before : WritesWithin observer upper values)
    (added : roots.NormalizedWithin observer (upper index)) :
    WritesWithin observer upper (values.set! index
      ((values[index]?.getD (.assigned .unknown)).join (.assigned roots))) := by
  intro cell bounded
  have originalBound : cell < values.size := by simpa using bounded
  change Write.NormalizedWithin observer (upper cell) ((values.set! index
    ((values[index]?.getD (.assigned .unknown)).join (.assigned roots)))[cell]?.getD (.assigned .unknown))
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases same : index = cell
  · subst cell
    simp only [originalBound, ite_true, Option.getD_some]
    exact (before index originalBound).join added
  · simp only [same, ite_false]
    exact before cell originalBound

theorem State.MemoryWithin.addSlot {observer : Func} {slotUpper contentUpper : Nat → List RootRef}
    {state : State} {slot : SlotId} {value : Roots}
    (before : state.MemoryWithin observer slotUpper contentUpper)
    (added : value.NormalizedWithin observer (slotUpper slot)) :
    ({ state with slots := addFlow state.slots slot value } : State).MemoryWithin observer slotUpper contentUpper :=
  { before with slots := before.slots.addFlow added }

theorem State.MemoryWithin.addContent {observer : Func} {slotUpper contentUpper : Nat → List RootRef}
    {state : State} {index : Nat} {value : Roots}
    (before : state.MemoryWithin observer slotUpper contentUpper)
    (added : value.NormalizedWithin observer (contentUpper index)) :
    ({ state with
      contents := addFlow state.contents index value
      writes := state.writes.set! index
        ((state.writes[index]?.getD (.assigned .unknown)).join (.assigned value)) } : State).MemoryWithin
      observer slotUpper contentUpper :=
  { before with contents := before.contents.addFlow added, writes := before.writes.assign added }

theorem State.MemoryWithin.touch {observer : Func} {slotUpper contentUpper : Nat → List RootRef}
    {state : State} (before : state.MemoryWithin observer slotUpper contentUpper) (roots : Roots) :
    ({ state with touched := roots } : State).MemoryWithin observer slotUpper contentUpper :=
  ⟨before.slots, before.contents, before.writes⟩

theorem State.MemoryWithin.write_known {observer f : Func} {slotUpper contentUpper : Nat → List RootRef}
    {state : State} {addresses : List Atom} {value : Roots}
    (before : state.MemoryWithin observer slotUpper contentUpper)
    (localBound : ∀ slot, Atom.local slot ∈ addresses → value.NormalizedWithin observer (slotUpper slot))
    (parameterBound : ∀ index, Atom.param index ∈ addresses →
      value.NormalizedWithin observer (contentUpper index)) :
    (write f state (.known addresses) value).MemoryWithin observer slotUpper contentUpper := by
  unfold write
  apply List.foldlRecOn (motive := fun (state : State) => state.MemoryWithin observer slotUpper contentUpper)
    addresses _ before
  intro current bounded address member
  cases address with
  | «local» slot => exact bounded.addSlot (localBound slot member)
  | global global => exact bounded.touch .unknown
  | contents index => exact bounded.touch .unknown
  | param index =>
      dsimp only
      split
      · exact bounded.addContent (parameterBound index member)
      · exact bounded

theorem State.MemoryWithin.write_ready {observer f : Func} {slotUpper contentUpper : Nat → List RootRef}
    {state : State} {address value : Roots}
    (before : state.MemoryWithin observer slotUpper contentUpper)
    (ready : address ≠ .unknown)
    (bounds : ∀ addresses, address = .known addresses →
      (∀ slot, Atom.local slot ∈ addresses → value.NormalizedWithin observer (slotUpper slot)) ∧
      (∀ index, Atom.param index ∈ addresses → value.NormalizedWithin observer (contentUpper index))) :
    (write f state address value).MemoryWithin observer slotUpper contentUpper := by
  cases address with
  | pending => exact before
  | unknown => exact False.elim (ready rfl)
  | known addresses => exact before.write_known (bounds addresses rfl).1 (bounds addresses rfl).2

theorem write_values (f : Func) (state : State) (address value : Roots) :
    (write f state address value).values = state.values := by
  cases address with
  | pending | unknown => rfl
  | known addresses =>
      unfold write
      apply List.foldlRecOn (motive := fun (current : State) => current.values = state.values) addresses _ rfl
      intro current preserved address _
      cases address <;> dsimp only <;> try exact preserved
      split <;> exact preserved

theorem write_returned (f : Func) (state : State) (address value : Roots) :
    (write f state address value).returned = state.returned := by
  cases address with
  | pending | unknown => rfl
  | known addresses =>
      unfold write
      apply List.foldlRecOn (motive := fun (current : State) => current.returned = state.returned) addresses _ rfl
      intro current preserved address _
      cases address <;> dsimp only <;> try exact preserved
      split <;> exact preserved

theorem start_memoryWithin (f : Func) (vt : Array (Option VTy))
    (slotUpper contentUpper : Nat → List RootRef)
    (ceilings : ∀ index row, f.roots.contents.find? (·.1 == index) = some row →
      row.2.flatMap f.expandParameterRoot ⊆ contentUpper index) :
    (start f vt).MemoryWithin f slotUpper contentUpper := by
  rw [start_components]
  constructor
  · intro index bounded
    have originalBound : index < f.slots.size := by simpa using bounded
    simpa [flowAt, originalBound] using Roots.NormalizedWithin.pending f (slotUpper index)
  · intro index bounded observed
    have parameterBound : index < f.params.length := by simpa using bounded
    have parameter : f.params[index]? = some f.params[index] := List.getElem?_eq_getElem parameterBound
    simp only [flowAt, Array.getElem?_mapIdx, List.getElem?_toArray, parameter, Option.map_some, Option.getD_some]
    split
    · cases found : f.roots.contents.find? (·.1 == index) with
      | none => simp [found] at observed
      | some row =>
          refine Or.inr ⟨unionRoots [] (row.2.flatMap f.expandParameterRoot), ?_, ?_⟩
          · simp [normalize, normalizeAtom, found]
          · intro root member
            exact ceilings index row found ((unionRoots_mem_iff _ _ _).mp member |>.resolve_left (by simp))
    · exact Roots.NormalizedWithin.known_empty f _
  · intro index bounded
    have originalBound : index < f.params.length := by simpa using bounded
    simp [Write.NormalizedWithin, originalBound]

#print axioms start_memoryWithin
#print axioms CellsWithin.addFlow
#print axioms WritesWithin.assign
#print axioms State.MemoryWithin.write_known
#print axioms State.MemoryWithin.write_ready
#print axioms write_values
#print axioms write_returned

end Goose.GIR.ReplacementContentFlow.Model
