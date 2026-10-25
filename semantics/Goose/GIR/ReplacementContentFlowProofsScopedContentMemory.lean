import Goose.GIR.ReplacementContentFlowProofsScopedCalls

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

structure State.ScopedMemoryWithin (state : State) (slots contents : Nat → Prop)
    (predicate : Atom → Prop) : Prop where
  slots : ∀ slot, slots slot → (flowAt state.slots slot).AtomsWithin predicate
  contents : ∀ index, contents index → (flowAt state.contents index).AtomsWithin predicate

structure State.ScopedContentWithin (state : State) (selected slots contents : Nat → Prop)
    (predicate : Atom → Prop) : Prop where
  values : state.ScopedValuesWithin selected predicate
  memory : state.ScopedMemoryWithin slots contents predicate

theorem State.ScopedMemoryWithin.of_extends {before after : State}
    {slots contents : Nat → Prop} {predicate : Atom → Prop}
    (growth : before.Extends after)
    (bounded : after.ScopedMemoryWithin slots contents predicate) :
    before.ScopedMemoryWithin slots contents predicate := by
  exact ⟨fun slot selected => (growth.slots.values slot).atomsWithin (bounded.slots slot selected),
    fun index selected => (growth.contents.values index).atomsWithin (bounded.contents index selected)⟩

theorem State.ScopedMemoryWithin.touchValues {state : State} {types : Array (Option VTy)}
    {values : List ValueId} {slots contents : Nat → Prop} {predicate : Atom → Prop}
    (bounded : state.ScopedMemoryWithin slots contents predicate) :
    (touchValues types state values).ScopedMemoryWithin slots contents predicate := ⟨bounded.slots, bounded.contents⟩

theorem State.ScopedMemoryWithin.addSlot {state : State} {slot : SlotId} {roots : Roots}
    {slots contents : Nat → Prop} {predicate : Atom → Prop}
    (bounded : state.ScopedMemoryWithin slots contents predicate)
    (added : slots slot → roots.AtomsWithin predicate) :
    ({state with slots := addFlow state.slots slot roots} : State).ScopedMemoryWithin
      slots contents predicate := by
  constructor
  · intro index selected
    rw [flowAt_addFlow]
    split
    · rename_i same
      have equality := same.1
      subst index
      exact (bounded.slots slot selected).join (added selected)
    · exact bounded.slots index selected
  · exact bounded.contents

theorem State.ScopedMemoryWithin.addContent {state : State} {index : Nat} {roots : Roots}
    {slots contents : Nat → Prop} {predicate : Atom → Prop}
    (bounded : state.ScopedMemoryWithin slots contents predicate)
    (added : contents index → roots.AtomsWithin predicate) :
    ({state with contents := addFlow state.contents index roots} : State).ScopedMemoryWithin
      slots contents predicate := by
  constructor
  · exact bounded.slots
  · intro parameter selected
    rw [flowAt_addFlow]
    split
    · rename_i same
      have equality := same.1
      subst parameter
      exact (bounded.contents index selected).join (added selected)
    · exact bounded.contents parameter selected

theorem write_known_scoped_memory {func : Func} {state : State} {addresses : List Atom} {roots : Roots}
    {slots contents : Nat → Prop} {predicate : Atom → Prop}
    (before : state.ScopedMemoryWithin slots contents predicate)
    (localValues : ∀ slot, slots slot → Atom.local slot ∈ addresses → roots.AtomsWithin predicate)
    (contentValues : ∀ index, contents index → Atom.param index ∈ addresses → roots.AtomsWithin predicate) :
    (write func state (.known addresses) roots).ScopedMemoryWithin slots contents predicate := by
  simp only [write]
  apply List.foldlRecOn (motive := fun current : State =>
    current.ScopedMemoryWithin slots contents predicate) addresses _ before
  intro current bounded atom member
  cases atom with
  | «local» slot =>
    dsimp only
    exact bounded.addSlot (fun selected => localValues slot selected member)
  | param index =>
    dsimp only
    split
    · have added := bounded.addContent (fun selected => contentValues index selected member)
      exact ⟨added.slots, added.contents⟩
    · exact ⟨bounded.slots, bounded.contents⟩
  | global index => exact ⟨bounded.slots, bounded.contents⟩
  | contents index => exact ⟨bounded.slots, bounded.contents⟩

theorem write_scoped_memory {func : Func} {state : State} {address roots : Roots}
    {slots contents : Nat → Prop} {predicate : Atom → Prop}
    (before : state.ScopedMemoryWithin slots contents predicate)
    (physical : address ≠ .unknown)
    (localValues : ∀ addresses, address = .known addresses → ∀ slot, slots slot →
      Atom.local slot ∈ addresses → roots.AtomsWithin predicate)
    (contentValues : ∀ addresses, address = .known addresses → ∀ index, contents index →
      Atom.param index ∈ addresses → roots.AtomsWithin predicate) :
    (write func state address roots).ScopedMemoryWithin slots contents predicate := by
  cases address with
  | pending => exact before
  | unknown => exact False.elim (physical rfl)
  | known addresses =>
      exact write_known_scoped_memory before (localValues addresses rfl) (contentValues addresses rfl)

theorem State.ScopedMemoryWithin.edge {func : Func} {state : State}
    {target : BlockId} {arguments : List ValueId} {slots contents : Nat → Prop} {predicate : Atom → Prop}
    (before : state.ScopedMemoryWithin slots contents predicate) :
    (edge func state target arguments).ScopedMemoryWithin slots contents predicate := by
  cases row : func.blocks[target]? with
  | none =>
      simp only [Model.edge, row]
      exact ⟨before.slots, before.contents⟩
  | some block =>
    simp only [Model.edge, row]
    apply List.foldlRecOn (motive := fun current : State =>
      current.ScopedMemoryWithin slots contents predicate) (block.params.zip arguments) _ before
    intro current bounded pair member
    exact ⟨bounded.slots, bounded.contents⟩

theorem HolderRoots.content_atomsWithin_typed {func : Func} {state : State} {payload : Ty}
    {upper : List RootRef} {address : Roots} {predicate : Atom → Prop}
    (physical : HolderRoots func payload upper address)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (reference : payload.isRefLike = true)
    (locals : ∀ slot storage, func.slots[slot]? = some storage → storage.ty = payload →
      RootRef.local slot ∈ upper → (flowAt state.slots slot).AtomsWithin predicate)
    (contents : ∀ index mutability, func.params[index]? = some (.ref mutability payload) →
      RootRef.param index ∈ upper → (flowAt state.contents index).AtomsWithin predicate) :
    (content func state address).AtomsWithin predicate := by
  cases address with
  | pending => trivial
  | unknown => exact False.elim physical
  | known atoms =>
      apply Roots.AtomsWithin.bind_known
      intro atom member
      cases physical atom member with
      | slot slot storage row type included => exact locals slot storage row type included
      | parameter index mutability row included =>
          have slice := paramOk_refLike_payload parameters row reference
          have found : (func.params[index]?).any Ty.isRefSlice = true := by simp [row, slice]
          simpa [found] using contents index mutability row included

theorem State.ScopedMemoryWithin.read {func : Func} {state : State} {payload : Ty}
    {upper : List RootRef} {address : Roots} {slots contents : Nat → Prop} {predicate : Atom → Prop}
    (bounded : state.ScopedMemoryWithin slots contents predicate)
    (physical : HolderRoots func payload upper address)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (reference : payload.isRefLike = true)
    (locals : ∀ slot storage, func.slots[slot]? = some storage → storage.ty = payload →
      RootRef.local slot ∈ upper → slots slot)
    (formals : ∀ index mutability, func.params[index]? = some (.ref mutability payload) →
      RootRef.param index ∈ upper → contents index) :
    (content func state address).AtomsWithin predicate :=
  physical.content_atomsWithin_typed parameters reference
    (fun slot storage row type included => bounded.slots slot (locals slot storage row type included))
    (fun index mutability row included => bounded.contents index (formals index mutability row included))

#print axioms write_known_scoped_memory
#print axioms write_scoped_memory
#print axioms State.ScopedMemoryWithin.edge
#print axioms HolderRoots.content_atomsWithin_typed
#print axioms State.ScopedMemoryWithin.read

end Goose.GIR.ReplacementContentFlow.Model
