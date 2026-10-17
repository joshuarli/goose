import Goose.GIR.ReplacementContentFlowProofsMemory
import Goose.GIR.ReplacementContentFlowProofsOrder

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem Roots.Extends.ready {before after : Roots} (growth : before.Extends after)
    (ready : before ≠ .pending) : after ≠ .pending := by
  cases before <;> cases after <;> simp_all [Roots.Extends]

theorem Roots.Extends.normalizedWithin {observer : Func} {before after : Roots}
    {upper : List RootRef} (growth : before.Extends after)
    (bounded : after.NormalizedWithin observer upper) :
    before.NormalizedWithin observer upper := by
  cases before with
  | pending => exact Or.inl rfl
  | unknown =>
      cases after <;> simp_all [Roots.Extends, Roots.NormalizedWithin, normalize]
  | known before =>
      cases after with
      | pending => simp [Roots.Extends] at growth
      | unknown => exact False.elim (bounded.not_unknown rfl)
      | known after =>
          obtain ⟨actual, known, within⟩ := bounded.actual (by simp)
          have atoms := (normalize_fold_atoms observer after [] actual known).2
          obtain ⟨result, normalized, valid⟩ := normalize_fold_within observer before upper (by
            intro atom member
            obtain ⟨roots, mapped, included⟩ := atoms atom (growth.subset member)
            exact ⟨roots, mapped, fun _ present => within (included present)⟩) [] (by simp)
          exact Or.inr ⟨result, normalized, valid⟩

theorem Write.Extends.normalizedWithin {observer : Func} {before after : Write}
    {upper : List RootRef} (growth : before.Extends after)
    (bounded : after.NormalizedWithin observer upper) :
    before.NormalizedWithin observer upper := by
  cases before with
  | unchanged => trivial
  | assigned before =>
      cases after with
      | unchanged => simp [Write.Extends] at growth
      | assigned after => exact Roots.Extends.normalizedWithin growth bounded

theorem CellsWithin.ofExtends {observer : Func} {upper : Nat → List RootRef}
    {before after : Array Roots} (growth : ArrayExtends .unknown Roots.Extends before after)
    (bounded : CellsWithin observer upper after) : CellsWithin observer upper before := by
  intro index member
  exact (growth.values index).normalizedWithin (bounded index (by simpa [growth.size] using member))

theorem ContentCellsWithin.ofExtends {observer : Func} {upper : Nat → List RootRef}
    {before after : Array Roots} (growth : ArrayExtends .unknown Roots.Extends before after)
    (bounded : ContentCellsWithin observer upper after) : ContentCellsWithin observer upper before := by
  intro index member observed
  exact (growth.values index).normalizedWithin
    (bounded index (by simpa [growth.size] using member) observed)

theorem WritesWithin.ofExtends {observer : Func} {upper : Nat → List RootRef}
    {before after : Array Write}
    (growth : ArrayExtends (.assigned .unknown) Write.Extends before after)
    (bounded : WritesWithin observer upper after) : WritesWithin observer upper before := by
  intro index member
  exact (growth.values index).normalizedWithin (bounded index (by simpa [growth.size] using member))

theorem State.Extends.memoryWithin {observer : Func} {slotUpper contentUpper : Nat → List RootRef}
    {before after : State} (growth : before.Extends after)
    (bounded : after.MemoryWithin observer slotUpper contentUpper) :
    before.MemoryWithin observer slotUpper contentUpper :=
  ⟨bounded.slots.ofExtends growth.slots, bounded.contents.ofExtends growth.contents,
    bounded.writes.ofExtends growth.writes⟩

#print axioms Roots.Extends.ready
#print axioms Roots.Extends.normalizedWithin
#print axioms Write.Extends.normalizedWithin
#print axioms CellsWithin.ofExtends
#print axioms ContentCellsWithin.ofExtends
#print axioms WritesWithin.ofExtends
#print axioms State.Extends.memoryWithin

end Goose.GIR.ReplacementContentFlow.Model
