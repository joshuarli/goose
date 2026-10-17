import Goose.GIR.ReplacementContentFlowProofsCanonicalRoots

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def Roots.AtomsWithin (predicate : Atom → Prop) : Roots → Prop
  | .pending => True
  | .known atoms => ∀ atom ∈ atoms, predicate atom
  | .unknown => False

theorem Roots.AtomsWithin.mono {before after : Atom → Prop} {roots : Roots}
    (bounded : roots.AtomsWithin before) (implies : ∀ atom, before atom → after atom) :
    roots.AtomsWithin after := by
  cases roots <;> simp_all [Roots.AtomsWithin]

theorem Roots.AtomsWithin.join {predicate : Atom → Prop} {left right : Roots}
    (leftBound : left.AtomsWithin predicate) (rightBound : right.AtomsWithin predicate) :
    (left.join right).AtomsWithin predicate := by
  cases left with
  | unknown => exact False.elim leftBound
  | pending => cases right <;> exact rightBound
  | known left =>
      cases right with
      | unknown => exact False.elim rightBound
      | pending => exact leftBound
      | known right =>
          obtain ⟨joined, same, within⟩ := join_known_subset left right
          rw [same]
          intro atom member
          exact (List.mem_append.mp (within member)).elim (leftBound atom) (rightBound atom)

theorem Roots.Extends.atomsWithin {predicate : Atom → Prop} {before after : Roots}
    (growth : before.Extends after) (bounded : after.AtomsWithin predicate) :
    before.AtomsWithin predicate := by
  cases before <;> cases after <;> simp_all [Roots.Extends, Roots.AtomsWithin]
  exact fun atom member => bounded atom (growth.subset member)

private theorem atomsWithin_strictMerge (predicate : Atom → Prop) (left right : Roots)
    (leftBound : left.AtomsWithin predicate) (rightBound : right.AtomsWithin predicate) :
    ((fun (left right : Roots) => match left, right with
      | .unknown, _ | _, .unknown => Roots.unknown
      | .pending, _ | _, .pending => .pending
      | left, right => left.join right) left right).AtomsWithin predicate := by
  cases left with
  | unknown => exact False.elim leftBound
  | pending => cases right <;> trivial
  | known left =>
      cases right with
      | unknown => exact False.elim rightBound
      | pending => trivial
      | known right => exact leftBound.join rightBound

theorem Roots.AtomsWithin.bind_known {predicate : Atom → Prop} (atoms : List Atom)
    (map : Atom → Roots) (mapped : ∀ atom ∈ atoms, (map atom).AtomsWithin predicate) :
    ((Roots.known atoms).bind map).AtomsWithin predicate := by
  dsimp only [Roots.bind]
  apply List.foldlRecOn (motive := fun (roots : Roots) => roots.AtomsWithin predicate)
    atoms _ (show (Roots.known []).AtomsWithin predicate from by simp [Roots.AtomsWithin])
  intro current bounded atom member
  exact atomsWithin_strictMerge predicate current (map atom) bounded (mapped atom member)

inductive HolderAtom (func : Func) (payload : Ty) (upper : List RootRef) : Atom → Prop
  | slot (slot : SlotId) (storage : Slot) (row : func.slots[slot]? = some storage)
      (type : storage.ty = payload) (member : RootRef.local slot ∈ upper) :
      HolderAtom func payload upper (.local slot)
  | parameter (index : Nat) (mutability : Mutability)
      (row : func.params[index]? = some (.ref mutability payload))
      (member : RootRef.param index ∈ upper) : HolderAtom func payload upper (.param index)

def HolderRoots (func : Func) (payload : Ty) (upper : List RootRef) (roots : Roots) : Prop :=
  roots.AtomsWithin (HolderAtom func payload upper)

theorem HolderAtom.local {func : Func} {payload : Ty} {upper : List RootRef} {slot : SlotId}
    (physical : HolderAtom func payload upper (.local slot)) :
    ∃ storage, func.slots[slot]? = some storage ∧ storage.ty = payload ∧ RootRef.local slot ∈ upper := by
  cases physical with
  | slot _ storage row type member => exact ⟨storage,row,type,member⟩

theorem HolderAtom.param {func : Func} {payload : Ty} {upper : List RootRef} {index : Nat}
    (physical : HolderAtom func payload upper (.param index)) :
    ∃ mutability, func.params[index]? = some (.ref mutability payload) ∧ RootRef.param index ∈ upper := by
  cases physical with
  | parameter _ mutability row member => exact ⟨mutability,row,member⟩

theorem HolderAtom.mono {func : Func} {payload : Ty} {small large : List RootRef} {atom : Atom}
    (bounded : HolderAtom func payload small atom) (subset : small ⊆ large) :
    HolderAtom func payload large atom := by
  cases bounded with
  | slot slot storage row type member => exact .slot slot storage row type (subset member)
  | parameter index mutability row member => exact .parameter index mutability row (subset member)

theorem HolderRoots.mono {func : Func} {payload : Ty} {small large : List RootRef} {roots : Roots}
    (bounded : HolderRoots func payload small roots) (subset : small ⊆ large) :
    HolderRoots func payload large roots := Roots.AtomsWithin.mono bounded (fun _ fact => HolderAtom.mono fact subset)

theorem HolderRoots.join {func : Func} {payload : Ty} {upper : List RootRef} {left right : Roots}
    (leftBound : HolderRoots func payload upper left)
    (rightBound : HolderRoots func payload upper right) :
    HolderRoots func payload upper (left.join right) := Roots.AtomsWithin.join leftBound rightBound

theorem HolderRoots.symbolic {func : Func} {payload : Ty} {upper : List RootRef} {roots : Roots}
    (bounded : HolderRoots func payload upper roots) : SymbolicRootsRefine func roots upper := by
  cases roots with
  | pending => exact .pending _ _
  | unknown => exact False.elim bounded
  | known atoms =>
      obtain ⟨actual, known, within⟩ := normalize_fold_within
        { func with roots := { func.roots with params := #[] } } atoms upper (by
          intro atom member
          cases bounded atom member with
          | slot slot storage row type included =>
              exact ⟨[.local slot], rfl, by simpa using included⟩
          | parameter index mutability row included =>
              exact ⟨[.param index], rfl, by simpa using included⟩) [] (by simp)
      exact Or.inr ⟨actual, known, fun root member => Or.inl (within member)⟩

theorem paramOk_refLike_payload {func : Func}
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    {index : Nat} {mutability : Mutability} {payload : Ty}
    (row : func.params[index]? = some (.ref mutability payload))
    (reference : payload.isRefLike = true) : (Ty.ref mutability payload).isRefSlice = true := by
  have valid := parameters (.ref mutability payload) (List.mem_of_getElem? row)
  cases payload <;> simp_all [Ty.paramOk, Ty.storable, Ty.refTarget, Ty.isRefLike, Ty.isRefSlice]

theorem HolderRoots.content_symbolic {func : Func} {state : State} {payload : Ty}
    {upper source : List RootRef} {address : Roots}
    (bounded : HolderRoots func payload upper address)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (reference : payload.isRefLike = true)
    (locals : ∀ slot, RootRef.local slot ∈ upper →
      SymbolicRootsRefine func (flowAt state.slots slot) source)
    (contents : ∀ index, RootRef.param index ∈ upper →
      SymbolicRootsRefine func (flowAt state.contents index) source) :
    SymbolicRootsRefine func (content func state address) source := by
  cases address with
  | pending => exact .pending _ _
  | unknown => exact False.elim bounded
  | known atoms =>
      apply SymbolicRootsRefine.bind_known
      intro atom member
      cases bounded atom member with
      | slot slot storage row type included => exact locals slot included
      | parameter index mutability row included =>
          have slice := paramOk_refLike_payload parameters row reference
          have found : (func.params[index]?).any Ty.isRefSlice = true := by simp [row, slice]
          simpa [found] using contents index included

theorem HolderRoots.content_symbolic_typed {func : Func} {state : State} {payload : Ty}
    {upper source : List RootRef} {address : Roots}
    (bounded : HolderRoots func payload upper address)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (reference : payload.isRefLike = true)
    (locals : ∀ slot storage, func.slots[slot]? = some storage → storage.ty = payload →
      RootRef.local slot ∈ upper → SymbolicRootsRefine func (flowAt state.slots slot) source)
    (contents : ∀ index mutability, func.params[index]? = some (.ref mutability payload) →
      RootRef.param index ∈ upper → SymbolicRootsRefine func (flowAt state.contents index) source) :
    SymbolicRootsRefine func (content func state address) source := by
  cases address with
  | pending => exact .pending _ _
  | unknown => exact False.elim bounded
  | known atoms =>
      apply SymbolicRootsRefine.bind_known
      intro atom member
      cases bounded atom member with
      | slot slot storage row type included => exact locals slot storage row type included
      | parameter index mutability row included =>
          have slice := paramOk_refLike_payload parameters row reference
          have found : (func.params[index]?).any Ty.isRefSlice = true := by simp [row, slice]
          simpa [found] using contents index mutability row included

theorem HolderRoots.content_reference {func : Func} {state : State} {payload : Ty}
    {mutability : Mutability} {upper : List RootRef} {address : Roots} {predicate : Atom → Prop}
    (physical : HolderRoots func (.ref mutability payload) upper address)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (slots : ∀ slot storage, func.slots[slot]? = some storage → storage.ty = .ref mutability payload →
      RootRef.local slot ∈ upper → (flowAt state.slots slot).AtomsWithin predicate) :
    (content func state address).AtomsWithin predicate := by
  cases address with
  | pending => trivial
  | unknown => exact False.elim physical
  | known atoms =>
      apply Roots.AtomsWithin.bind_known
      intro atom member
      cases physical atom member with
      | slot slot storage row type included => exact slots slot storage row type included
      | parameter index sourceMutability row included =>
          have impossible := paramOk_refLike_payload parameters row (by simp [Ty.isRefLike])
          simp [Ty.isRefSlice] at impossible

#print axioms HolderRoots.content_symbolic
#print axioms HolderRoots.symbolic
#print axioms paramOk_refLike_payload

end Goose.GIR.ReplacementContentFlow.Model
