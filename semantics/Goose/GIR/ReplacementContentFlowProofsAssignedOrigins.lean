import Goose.GIR.ReplacementContentFlowProofsOrder

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def Write.AssignedAt (writes : Array Write) (index : Nat) : Prop :=
  ∃ roots, writes[index]? = some (.assigned roots)

theorem Write.assignedAt_set_join (writes : Array Write) (index target : Nat) (roots : Roots) :
    AssignedAt (writes.set! target
      ((writes[target]?.getD (.assigned .unknown)).join (.assigned roots))) index ↔
      AssignedAt writes index ∨ index = target ∧ index < writes.size := by
  simp only [AssignedAt, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases same : target = index
  · subst target
    by_cases bound : index < writes.size
    · simp only [bound, and_self, ite_true, Option.some.injEq, or_true]
      cases writes[index]?.getD (.assigned .unknown) <;> simp [Write.join]
    · have absent : writes[index]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
      simp [bound]
  · simp [same, Ne.symm same]

theorem write_known_assigned_origin (func : Func) (state : State)
    (addresses : List Atom) (value : Roots) (index : Nat) :
    Write.AssignedAt (write func state (.known addresses) value).writes index ↔
      Write.AssignedAt state.writes index ∨
        .param index ∈ addresses ∧ index < state.writes.size ∧
          (func.params[index]?).any Ty.isRefSlice = true := by
  induction addresses generalizing state with
  | nil => simp [write]
  | cons atom addresses ih =>
    simp only [write, List.foldl_cons]
    simp only [write] at ih
    rw [ih]
    cases atom with
    | «local» slot => simp
    | global global => simp
    | contents content => simp
    | param parameter =>
      by_cases slice : (func.params[parameter]?).any Ty.isRefSlice = true
      · simp only [slice, ite_true, Write.assignedAt_set_join, Array.size_set!, List.mem_cons,
          Atom.param.injEq]
        by_cases same : parameter = index
        · subst parameter
          simp only [slice, true_or, true_and, and_true]
          constructor
          · rintro (h | ⟨_, h⟩)
            · exact h
            · exact Or.inr h
          · exact Or.inl
        · simp [Ne.symm same]
      · simp only [show (func.params[parameter]?).any Ty.isRefSlice = false from
          Bool.eq_false_iff.mpr slice, List.mem_cons, Atom.param.injEq]
        by_cases same : parameter = index
        · subst parameter
          simp [slice]
        · simp [Ne.symm same]

theorem write_assigned_origin (func : Func) (state : State) (address value : Roots)
    (index : Nat) (safe : address ≠ .unknown)
    (assigned : Write.AssignedAt (write func state address value).writes index) :
    Write.AssignedAt state.writes index ∨
      ∃ atoms, address = .known atoms ∧ .param index ∈ atoms ∧
        index < state.writes.size ∧ (func.params[index]?).any Ty.isRefSlice = true := by
  cases address with
  | pending => exact Or.inl assigned
  | unknown => exact False.elim (safe rfl)
  | known atoms =>
    rcases (write_known_assigned_origin func state atoms value index).mp assigned with old | fresh
    · exact Or.inl old
    · exact Or.inr ⟨atoms, rfl, fresh⟩

theorem Write.AssignedAt.extends {before after : Array Write} {index : Nat}
    (growth : ArrayExtends (.assigned .unknown) Write.Extends before after)
    (assigned : AssignedAt before index) : AssignedAt after index := by
  obtain ⟨roots, found⟩ := assigned
  have bound : index < before.size := Array.getElem?_eq_some_iff.mp found |>.1
  have afterBound : index < after.size := by simpa [growth.size] using bound
  have one := growth.values index
  rw [found] at one
  cases next : after[index]? with
  | none => simp [Array.getElem?_eq_getElem afterBound] at next
  | some row =>
      cases row with
      | unchanged => simp [next, Write.Extends] at one
      | assigned roots => exact ⟨roots, next⟩

#print axioms write_known_assigned_origin
#print axioms Write.AssignedAt.extends

end Goose.GIR.ReplacementContentFlow.Model
