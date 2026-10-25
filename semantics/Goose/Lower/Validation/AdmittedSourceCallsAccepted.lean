import Goose.Lower.Validation.AdmittedSourceCallsReceivers
import Goose.Lower.Validation.SummaryPreservationSlotSeedRetention

namespace Goose.Lower.Validation.AdmittedSourceCalls

open Goose.Core Goose.GIR

theorem accepted_slot_ceiling_bounds {module : Core.Module} {context : Context} {impl : Impl}
    {contextId : ContextId} {slot : SlotId} {localVar : LocalVar} {ceiling : List RootRef}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextId]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    (variableAt : impl.vars[slot]? = some localVar)
    (reference : localVar.ty.isRefLike = true) (ordinary : localVar.ty.isRefSlice = false)
    (annotation : (slot, ceiling) ∈ context.varRoots) :
    let actual := rootsAt ((lowerContextAt module context impl).provenance
      (resultRoots (lower module) (lower module).implTypes)
      ((lowerContextAt module context impl).valueTypes (lower module))
      (lower module).rootCount).slots slot
    GIR.RootsRefine (lowerContextAt module context impl) actual ceiling ∧ ceiling ⊆ actual := by
  have metadata : (slot, lowerContextRootCeiling context impl ceiling) ∈
      (lowerContextAt module context impl).roots.slots.getD #[] := by
    change (slot, lowerContextRootCeiling context impl ceiling) ∈
      (context.varRoots.filterMap _).toArray
    apply Array.mem_toList_iff.mp
    apply List.mem_filterMap.mpr
    exact ⟨(slot, ceiling), annotation, by simp [variableAt, reference, ordinary]⟩
  have equivalent := SummaryPreservation.accepted_function_provenance_slot_row_iff
    accepted contextAt implAt metadata
  constructor
  · intro root member
    exact lowerContextRootCeiling_refines module context impl ceiling root ((equivalent root).mp member)
  · intro root member
    exact (equivalent root).mpr (Core.Sound.unionRoots_left _ _ _ member)

#print axioms accepted_slot_ceiling_bounds

end Goose.Lower.Validation.AdmittedSourceCalls
