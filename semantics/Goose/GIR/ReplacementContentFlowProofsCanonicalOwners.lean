import Goose.GIR.ReplacementContentFlowProofsCanonicalHolders

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def LocalOwnerAddresses (func : Func) (payload : Ty) (roots : Roots) : Prop :=
  roots.AtomsWithin fun atom => ∀ slot, atom = .local slot →
    ∃ storage, func.slots[slot]? = some storage ∧ storage.ty = payload

inductive OwnerOrigin (func : Func) (payload : Ty) : Atom → Prop
  | slot (slot : SlotId) (storage : Slot) (row : func.slots[slot]? = some storage)
      (type : storage.ty = payload) : OwnerOrigin func payload (.local slot)
  | global (global : GlobalId) : OwnerOrigin func payload (.global global)
  | parameter (index : Nat) (mutability : Mutability)
      (row : func.params[index]? = some (.ref mutability payload)) : OwnerOrigin func payload (.param index)

def OwnerOrigins (func : Func) (payload : Ty) (roots : Roots) : Prop :=
  roots.AtomsWithin (OwnerOrigin func payload)

def OwnerValues (func : Func) (vt : Array (Option VTy)) (values : Array Roots) : Prop :=
  ∀ value, value < values.size → ∀ mutability payload,
    vt[value]? = some (some (.data (.ref mutability payload))) → payload.ownerElem?.isSome = true →
      OwnerOrigins func payload (flowAt values value)

def OwnerSlots (func : Func) (values : Array Roots) : Prop :=
  ∀ slot storage, func.slots[slot]? = some storage → slot < values.size → ∀ mutability payload,
    storage.ty = .ref mutability payload → payload.ownerElem?.isSome = true →
      OwnerOrigins func payload (flowAt values slot)

theorem OwnerOrigin.local {func : Func} {payload : Ty} {slot : SlotId}
    (origin : OwnerOrigin func payload (.local slot)) :
    ∃ storage, func.slots[slot]? = some storage ∧ storage.ty = payload := by
  cases origin with
  | slot _ storage row type => exact ⟨storage,row,type⟩

theorem OwnerOrigin.param {func : Func} {payload : Ty} {index : Nat}
    (origin : OwnerOrigin func payload (.param index)) :
    ∃ mutability, func.params[index]? = some (.ref mutability payload) := by
  cases origin with
  | parameter _ mutability row => exact ⟨mutability,row⟩

theorem OwnerOrigins.localAddresses {func : Func} {payload : Ty} {roots : Roots}
    (origins : OwnerOrigins func payload roots) : LocalOwnerAddresses func payload roots := by
  apply Roots.AtomsWithin.mono origins
  intro atom origin slot same
  subst atom
  exact origin.local

theorem OwnerOrigins.join {func : Func} {payload : Ty} {left right : Roots}
    (leftOrigins : OwnerOrigins func payload left) (rightOrigins : OwnerOrigins func payload right) :
    OwnerOrigins func payload (left.join right) := Roots.AtomsWithin.join leftOrigins rightOrigins

theorem LocalOwnerAddresses.join {func : Func} {payload : Ty} {left right : Roots}
    (leftOrigins : LocalOwnerAddresses func payload left) (rightOrigins : LocalOwnerAddresses func payload right) :
    LocalOwnerAddresses func payload (left.join right) := Roots.AtomsWithin.join leftOrigins rightOrigins

theorem OwnerValues.set {func : Func} {vt : Array (Option VTy)} {values : Array Roots}
    {index : Nat} {roots : Roots} (before : OwnerValues func vt values)
    (added : ∀ mutability payload, vt[index]? = some (some (.data (.ref mutability payload))) →
      payload.ownerElem?.isSome = true → OwnerOrigins func payload roots) :
    OwnerValues func vt (values.set! index roots) := by
  intro value bounded mutability payload type owner
  have priorBound : value < values.size := by simpa using bounded
  change OwnerOrigins func payload ((values.set! index roots)[value]?.getD .unknown)
  simp only [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds]
  by_cases same : index = value
  · subst value
    simpa [priorBound] using added mutability payload type owner
  · simpa [same,flowAt] using before value priorBound mutability payload type owner

theorem OwnerValues.addFlow {func : Func} {vt : Array (Option VTy)} {values : Array Roots}
    {index : Nat} {roots : Roots} (before : OwnerValues func vt values)
    (added : ∀ mutability payload, vt[index]? = some (some (.data (.ref mutability payload))) →
      payload.ownerElem?.isSome = true → OwnerOrigins func payload roots) :
    OwnerValues func vt (addFlow values index roots) := by
  intro value bounded mutability payload type owner
  have priorBound : value < values.size := by simpa [ReplacementContentFlow.Model.addFlow] using bounded
  rw [flowAt_addFlow]
  split
  · rename_i updated
    have same := updated.1
    subst value
    exact (before index priorBound mutability payload type owner).join (added mutability payload type owner)
  · exact before value priorBound mutability payload type owner

theorem OwnerSlots.addFlow {func : Func} {values : Array Roots} {index : Nat} {roots : Roots}
    (before : OwnerSlots func values)
    (added : ∀ storage, func.slots[index]? = some storage → ∀ mutability payload,
      storage.ty = .ref mutability payload → payload.ownerElem?.isSome = true → OwnerOrigins func payload roots) :
    OwnerSlots func (addFlow values index roots) := by
  intro slot storage row bounded mutability payload type owner
  have priorBound : slot < values.size := by simpa [ReplacementContentFlow.Model.addFlow] using bounded
  rw [flowAt_addFlow]
  split
  · rename_i updated
    have same := updated.1
    subst slot
    exact (before index storage row priorBound mutability payload type owner).join
      (added storage row mutability payload type owner)
  · exact before slot storage row priorBound mutability payload type owner

theorem start_ownerSlots (func : Func) (vt : Array (Option VTy)) : OwnerSlots func (start func vt).slots := by
  rw [start_components]
  intro slot storage _ bounded mutability payload _ _
  have bound : slot < func.slots.size := by simpa using bounded
  simp [OwnerOrigins,Roots.AtomsWithin,flowAt,bound]

theorem start_ownerValues (func : Func) (vt : Array (Option VTy))
    (parameters : ∀ entry : Block, func.blocks[0]? = some entry →
      ∀ pair index, (pair,index) ∈ entry.params.zipIdx →
        ∃ type, pair.2 = .data type ∧ vt[pair.1]? = some (some (.data type)) ∧
          func.params[index]? = some type) : OwnerValues func vt (start func vt).values := by
  cases found : func.blocks[0]? with
  | none =>
      intro value bounded mutability payload type owner
      have bound : value < func.numValues := by simpa [start,found] using bounded
      simp [start,found,OwnerOrigins,Roots.AtomsWithin,flowAt,bound]
  | some entry =>
      rw [start_values_fold vt found]
      have base : OwnerValues func vt (Array.replicate func.numValues .pending) := by
        intro value bounded mutability payload type owner
        have bound : value < func.numValues := by simpa using bounded
        simp [OwnerOrigins,Roots.AtomsWithin,flowAt,bound]
      apply List.foldlRecOn (motive := fun values : Array Roots => OwnerValues func vt values)
        entry.params.zipIdx _ base
      intro values before pair member
      apply before.set
      intro mutability payload type owner
      obtain ⟨declared,_,canonical,formal⟩ := parameters entry found pair.1 pair.2 member
      have identical : declared = .ref mutability payload := by
        rw [canonical] at type
        exact VTy.data.inj (Option.some.inj (Option.some.inj type))
      subst declared
      have like : valRefLike vt pair.1.1 = true := by
        simp [valRefLike,canonical,VTy.refLike,Ty.isRefLike]
      simp only [like,ite_true]
      intro atom included
      have identical : atom = .param pair.2 := by simpa using included
      subst atom
      exact .parameter pair.2 mutability formal

theorem OwnerOrigins.normalizedLocal {func : Func} {payload : Ty} {roots : Roots}
    {actual : List RootRef} {slot : SlotId}
    (origins : OwnerOrigins func payload roots)
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (known : normalize func roots = some actual) (member : RootRef.local slot ∈ actual) :
    ∃ storage, func.slots[slot]? = some storage ∧ storage.ty = payload := by
  obtain ⟨atoms,rfl⟩ := normalize_known_shape known
  obtain ⟨atom,atomMember,mapped,mappedKnown,mappedMember⟩ := (normalize_known_members known (.local slot)).mp member
  cases origins atom atomMember with
  | slot address storage row type =>
      have identity : mapped = [.local address] := Option.some.inj mappedKnown.symm
      subst mapped
      have same : address = slot := by
        have same : RootRef.local slot = .local address := by simpa using mappedMember
        exact (RootRef.local.inj same).symm
      subst address
      exact ⟨storage,row,type⟩
  | global global =>
      have identity : mapped = [.global global] := Option.some.inj mappedKnown.symm
      subst mapped
      simp at mappedMember
  | parameter index mutability row =>
      have identity : mapped = func.parameterRoots index := Option.some.inj mappedKnown.symm
      subst mapped
      rcases closed index (.local slot) mappedMember with impossible | ⟨global,impossible⟩ <;> cases impossible

theorem OwnerOrigins.substitute {caller callee : Func} {payload : Ty} {state : State}
    {args : List ValueId} {roots : Roots} {ceiling : List RootRef}
    (origins : OwnerOrigins callee payload roots)
    (bounded : SymbolicRootsRefine callee roots ceiling)
    (external : ∀ slot, RootRef.local slot ∉ ceiling)
    (arguments : ∀ (index : Nat) (mutability : Mutability),
      callee.params[index]? = some (.ref mutability payload) →
      ∃ value, args[index]? = some value ∧ OwnerOrigins caller payload (flowAt state.values value)) :
    OwnerOrigins caller payload (substitute caller state args roots) := by
  cases roots with
  | pending => trivial
  | unknown => exact False.elim origins
  | known atoms =>
      apply Roots.AtomsWithin.bind_known
      intro atom member
      cases origins atom member with
      | slot slot storage row type => exact False.elim (bounded.local_not_mem external slot member)
      | global global =>
          intro atom member
          have same : atom = .global global := by simpa using member
          subst atom
          exact .global global
      | parameter index mutability row =>
          obtain ⟨value,argumentRow,actual⟩ := arguments index mutability row
          simpa only [argumentRow,Option.map_some,Option.getD_some,OwnerOrigins] using actual

#print axioms OwnerOrigins.normalizedLocal

end Goose.GIR.ReplacementContentFlow.Model
