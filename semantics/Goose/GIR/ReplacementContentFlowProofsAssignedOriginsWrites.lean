import Goose.GIR.ReplacementContentFlowProofsAssignedOrigins

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem Roots.Extends.nonpending {before after : Roots}
    (growth : before.Extends after) (ready : before ≠ .pending) : after ≠ .pending := by
  cases before <;> cases after <;> simp_all [Roots.Extends]

theorem Roots.join_nonpending_right (left right : Roots) (ready : right ≠ .pending) :
    left.join right ≠ .pending := by
  cases left <;> cases right <;> simp_all [Roots.join]

def Write.ReadyAt (writes : Array Write) (index : Nat) : Prop :=
  ∃ roots, writes[index]? = some (.assigned roots) ∧ roots ≠ .pending

theorem Write.ReadyAt.extends {before after : Array Write} {index : Nat}
    (growth : ArrayExtends (.assigned .unknown) Write.Extends before after)
    (ready : ReadyAt before index) : ReadyAt after index := by
  obtain ⟨roots, found, ready⟩ := ready
  have next := Write.AssignedAt.extends growth ⟨roots, found⟩
  obtain ⟨nextRoots, nextFound⟩ := next
  have one := growth.values index
  simp only [found, nextFound, Option.getD_some, Write.Extends] at one
  exact ⟨nextRoots, nextFound, one.nonpending ready⟩

theorem write_known_parameter_ready (func : Func) (state : State)
    (addresses : List Atom) (value : Roots) (index : Nat)
    (member : .param index ∈ addresses) (bounded : index < state.writes.size)
    (reference : (func.params[index]?).any Ty.isRefSlice = true)
    (ready : value ≠ .pending) :
    Write.ReadyAt (write func state (.known addresses) value).writes index := by
  induction addresses generalizing state with
  | nil => simp at member
  | cons atom addresses ih =>
    rcases List.mem_cons.mp member with same | later
    · subst atom
      let middle : State := { state with
        contents := addFlow state.contents index value
        writes := state.writes.set! index
          ((state.writes[index]?.getD (.assigned .unknown)).join (.assigned value)) }
      have middleReady : Write.ReadyAt middle.writes index := by
        have present : middle.writes[index]? = some
            ((state.writes[index]?.getD (.assigned .unknown)).join (.assigned value)) := by
          simp [middle, bounded]
        cases old : state.writes[index]?.getD (.assigned .unknown) with
        | unchanged => exact ⟨value, by simpa [old, Write.join] using present, ready⟩
        | assigned roots =>
          exact ⟨roots.join value, by simpa [old, Write.join] using present,
            Roots.join_nonpending_right roots value ready⟩
      exact middleReady.extends (by
        simpa only [write, List.foldl_cons, reference, ite_true, middle]
          using (write_extends func middle (.known addresses) value).writes)
    · have stepBound : index < (write func state (.known [atom]) value).writes.size := by
        rw [← (write_extends func state (.known [atom]) value).writes.size]
        exact bounded
      have tail := ih (write func state (.known [atom]) value) later stepBound
      simpa only [write, List.foldl_cons, List.foldl_nil] using tail

#print axioms write_known_parameter_ready
#print axioms Write.ReadyAt.extends

end Goose.GIR.ReplacementContentFlow.Model
