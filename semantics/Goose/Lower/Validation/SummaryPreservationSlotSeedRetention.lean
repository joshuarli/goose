import Goose.Lower.Validation.ReplacementProvenance
import Goose.Lower.Validation.SummaryPreservationAcceptedSlots

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem slotRootSeeds_row {func : Func} {row : SlotId × List RootRef} {storage : Slot}
    (member : row ∈ func.roots.slots.getD #[])
    (slotRow : func.slots[row.1]? = some storage) :
    ∀ root ∈ row.2, root ∈ rootsAt func.slotRootSeeds row.1 := by
  intro root rootMember
  simp only [rootsAt, Func.slotRootSeeds, Array.getElem?_mapIdx, slotRow,
    Option.map_some, Option.getD_some]
  rw [← Array.foldl_toList]
  apply list_foldl_establishes
    (property := fun _ : List RootRef => True) (known := fun roots => root ∈ roots)
    ((func.roots.slots.getD #[]).toList) []
    (fun roots entry => if entry.1 == row.1 then unionRoots roots entry.2 else roots)
    row (Array.mem_toList_iff.mpr member) trivial
  · intros; trivial
  · intro roots entry retained
    split
    · exact unionRoots_left _ _ _ retained
    · exact retained
  · intro roots _
    simp only [beq_self_eq_true, ite_true]
    exact unionRoots_right _ _ _ rootMember

theorem provenance_retains_slot_seeds (results : Array (List RootRef))
    (types : Array (Option VTy)) (func : Func) (rootCount : Nat) :
    ∀ slot root, root ∈ rootsAt func.slotRootSeeds slot →
      root ∈ rootsAt (func.provenance results types rootCount).slots slot := by
  have retained := provFix_extends results types func
    ((func.numValues + func.slots.size + 1) * (rootCount + 1)) (provStart types func)
  exact retained.2.2.1

theorem accepted_function_provenance_slot_row_iff {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} {row : SlotId × List RootRef} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (rowMember : row ∈ (lowerContextAt module ctx impl).roots.slots.getD #[]) (root : RootRef) :
    root ∈ rootsAt ((lowerContextAt module ctx impl).provenance
      (resultRoots (lower module) (lower module).implTypes)
      ((lowerContextAt module ctx impl).valueTypes (lower module)) (lower module).rootCount).slots row.1 ↔
      root ∈ row.2 := by
  constructor
  · exact accepted_function_provenance_slots_declared accepted contextRow implementationRow row rowMember root
  · intro member
    obtain ⟨storage, slotRow, _⟩ := lowerContext_declared_slot_reference rowMember
    exact provenance_retains_slot_seeds _ _ _ _ row.1 root (slotRootSeeds_row rowMember slotRow root member)

#print axioms slotRootSeeds_row
#print axioms provenance_retains_slot_seeds
#print axioms accepted_function_provenance_slot_row_iff

end Goose.Lower.Validation.SummaryPreservation
