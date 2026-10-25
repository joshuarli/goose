import Goose.GIR.AdmittedRegions
import Goose.Lower.Validation.SummaryPreservationAcceptedSlots

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem accepted_function_admittedSlots {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl) :
    (lowerContextAt module ctx impl).admittedSlots
      ((lowerContextAt module ctx impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module ctx impl).valueTypes (lower module)) (lower module).rootCount) = true := by
  apply List.all_eq_true.mpr
  intro row member
  have rowMember := Array.mem_toList_iff.mp member
  obtain ⟨storage, storageRow, reference⟩ := lowerContext_declared_slot_reference rowMember
  change ((lowerContextAt module ctx impl).slots[row.1]?).any (fun storage =>
    storage.ty.isRefLike && (rootsAt ((lowerContextAt module ctx impl).provenance
      (resultRoots (lower module) (lower module).implTypes)
      ((lowerContextAt module ctx impl).valueTypes (lower module)) (lower module).rootCount).slots row.1).all row.2.contains) = true
  simp only [storageRow, Option.any_some, reference, Bool.true_and, List.all_eq_true, List.contains_iff_mem]
  exact accepted_function_provenance_slots_declared accepted contextRow implementationRow row rowMember

theorem lowerGlobal_admittedSlots (module : Core.Module) (global : Core.Global) (provenance : Prov) :
    (lowerGlobal module global).init.admittedSlots provenance = true := rfl

#print axioms accepted_function_admittedSlots
#print axioms lowerGlobal_admittedSlots

end Goose.Lower.Validation.SummaryPreservation
