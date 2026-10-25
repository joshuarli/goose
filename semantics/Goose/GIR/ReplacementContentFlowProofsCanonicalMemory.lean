import Goose.GIR.ReplacementContentFlowProofsCanonicalHolders

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def SymbolicCells (func : Func) (upper : Nat → List RootRef) (cells : Array Roots) : Prop :=
  ∀ index, index < cells.size → SymbolicRootsRefine func (flowAt cells index) (upper index)

def SymbolicContentCells (func : Func) (cells : Array Roots) : Prop :=
  ∀ index, index < cells.size →
    (func.roots.contents.find? (·.1 == index)).isSome = true →
      SymbolicRootsRefine func (flowAt cells index) (func.contentRoots index)

def Write.SymbolicRefine (func : Func) (upper : List RootRef) : Write → Prop
  | .unchanged => True
  | .assigned roots => SymbolicRootsRefine func roots upper

def SymbolicWrites (func : Func) (cells : Array Write) : Prop :=
  ∀ index, index < cells.size →
    (cells[index]?.getD (.assigned .unknown)).SymbolicRefine func (func.contentRoots index)

structure State.CanonicalMemory (func : Func) (provenance : Prov) (state : State) : Prop where
  slots : SymbolicCells func (rootsAt provenance.slots) state.slots
  contents : SymbolicContentCells func state.contents
  writes : SymbolicWrites func state.writes

theorem SymbolicCells.addFlow {func : Func} {upper : Nat → List RootRef}
    {cells : Array Roots} {index : Nat} {roots : Roots}
    (before : SymbolicCells func upper cells)
    (added : SymbolicRootsRefine func roots (upper index)) :
    SymbolicCells func upper (addFlow cells index roots) := by
  intro cell bounded
  have originalBound : cell < cells.size := by simpa [ReplacementContentFlow.Model.addFlow] using bounded
  rw [flowAt_addFlow]
  split
  · rename_i updated
    have same := updated.1
    subst cell
    exact (before index originalBound).join added
  · exact before cell originalBound

theorem SymbolicContentCells.addFlow {func : Func} {cells : Array Roots} {index : Nat} {roots : Roots}
    (before : SymbolicContentCells func cells)
    (added : SymbolicRootsRefine func roots (func.contentRoots index)) :
    SymbolicContentCells func (addFlow cells index roots) := by
  intro cell bounded observed
  have originalBound : cell < cells.size := by simpa [ReplacementContentFlow.Model.addFlow] using bounded
  rw [flowAt_addFlow]
  split
  · rename_i updated
    have same := updated.1
    subst cell
    exact (before index originalBound observed).join added
  · exact before cell originalBound observed

theorem Write.SymbolicRefine.join {func : Func} {upper : List RootRef} {left right : Write}
    (leftBound : left.SymbolicRefine func upper) (rightBound : right.SymbolicRefine func upper) :
    (left.join right).SymbolicRefine func upper := by
  cases left <;> cases right <;> simp_all only [Write.SymbolicRefine, Write.join]
  exact leftBound.join rightBound

theorem SymbolicWrites.assign {func : Func} {cells : Array Write} {index : Nat} {roots : Roots}
    (before : SymbolicWrites func cells)
    (added : SymbolicRootsRefine func roots (func.contentRoots index)) :
    SymbolicWrites func (cells.set! index
      ((cells[index]?.getD (.assigned .unknown)).join (.assigned roots))) := by
  intro cell bounded
  have originalBound : cell < cells.size := by simpa using bounded
  change Write.SymbolicRefine func (func.contentRoots cell) ((cells.set! index
    ((cells[index]?.getD (.assigned .unknown)).join (.assigned roots)))[cell]?.getD (.assigned .unknown))
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases same : index = cell
  · subst cell
    simp only [originalBound, ite_true, Option.getD_some]
    exact (before index originalBound).join added
  · simp only [same, ite_false]
    exact before cell originalBound

theorem State.CanonicalMemory.addSlot {func : Func} {provenance : Prov} {state : State}
    {slot : SlotId} {value : Roots} (before : state.CanonicalMemory func provenance)
    (added : SymbolicRootsRefine func value (rootsAt provenance.slots slot)) :
    ({ state with slots := addFlow state.slots slot value } : State).CanonicalMemory func provenance :=
  { before with slots := before.slots.addFlow added }

theorem State.CanonicalMemory.addContent {func : Func} {provenance : Prov} {state : State}
    {index : Nat} {value : Roots} (before : state.CanonicalMemory func provenance)
    (added : SymbolicRootsRefine func value (func.contentRoots index)) :
    ({ state with
      contents := addFlow state.contents index value
      writes := state.writes.set! index
        ((state.writes[index]?.getD (.assigned .unknown)).join (.assigned value)) } : State).CanonicalMemory
      func provenance :=
  { before with contents := before.contents.addFlow added, writes := before.writes.assign added }

theorem State.CanonicalMemory.touch {func : Func} {provenance : Prov} {state : State}
    (before : state.CanonicalMemory func provenance) (roots : Roots) :
    ({ state with touched := roots } : State).CanonicalMemory func provenance :=
  ⟨before.slots, before.contents, before.writes⟩

theorem State.CanonicalMemory.write {func : Func} {provenance : Prov} {state : State}
    {payload : Ty} {upper : List RootRef} {address value : Roots}
    (before : state.CanonicalMemory func provenance)
    (physical : HolderRoots func payload upper address)
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (reference : payload.isRefLike = true)
    {valueUpper : List RootRef} (valueBound : SymbolicRootsRefine func value valueUpper)
    (localBound : ∀ slot storage, func.slots[slot]? = some storage → storage.ty = payload →
      RootRef.local slot ∈ upper → RootsRefine func valueUpper (rootsAt provenance.slots slot))
    (parameterBound : ∀ index mutability, func.params[index]? = some (.ref mutability payload) →
      RootRef.param index ∈ upper → RootsRefine func valueUpper (func.contentRoots index)) :
    (write func state address value).CanonicalMemory func provenance := by
  cases address with
  | pending => exact before
  | unknown => exact False.elim physical
  | known atoms =>
      simp only [ReplacementContentFlow.Model.write]
      apply List.foldlRecOn (motive := fun (current : State) => current.CanonicalMemory func provenance)
        atoms _ before
      intro current bounded atom member
      cases physical atom member with
      | slot slot storage row type included =>
          exact bounded.addSlot (valueBound.refine closed (localBound slot storage row type included))
      | parameter index mutability row included =>
          have slice := paramOk_refLike_payload parameters row reference
          have found : (func.params[index]?).any Ty.isRefSlice = true := by simp [row, slice]
          simp only [found, ite_true]
          exact bounded.addContent (valueBound.refine closed (parameterBound index mutability row included))

theorem State.Extends.canonicalMemory {func : Func} {provenance : Prov} {before after : State}
    (growth : before.Extends after) (bounded : after.CanonicalMemory func provenance) :
    before.CanonicalMemory func provenance := by
  constructor
  · intro index member
    exact (growth.slots.values index).symbolicRootsRefine
      (bounded.slots index (by simpa [growth.slots.size] using member))
  · intro index member observed
    exact (growth.contents.values index).symbolicRootsRefine
      (bounded.contents index (by simpa [growth.contents.size] using member) observed)
  · intro index member
    have prior := bounded.writes index (by simpa [growth.writes.size] using member)
    have grows := growth.writes.values index
    cases beforeRow : before.writes[index]?.getD (.assigned .unknown) with
    | unchanged => trivial
    | assigned roots =>
        cases afterRow : after.writes[index]?.getD (.assigned .unknown) with
        | unchanged => simp [beforeRow, afterRow, Write.Extends] at grows
        | assigned result =>
            rw [beforeRow, afterRow] at grows
            rw [afterRow] at prior
            exact Roots.Extends.symbolicRootsRefine grows prior

#print axioms State.CanonicalMemory.write
#print axioms State.Extends.canonicalMemory

end Goose.GIR.ReplacementContentFlow.Model
