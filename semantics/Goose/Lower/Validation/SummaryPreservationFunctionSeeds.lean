import Goose.Lower.Validation.SummaryPreservationDeclaredSeeds
import Goose.Lower.Validation.SummaryPreservationFunctionEntryFrame
import Goose.Lower.Validation.ValidationTypedModuleTables

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem accepted_context_entry_type {module : Core.Module} {ctx : Context} {impl : Impl}
    {implementation : ImplId} {index : Nat} {type : VTy}
    (accepted : Core.validate module = .ok ())
    (implementationRow : module.impls[implementation]? = some impl)
    (row : (impl.params.toList.map fun param => VTy.data (tyOfVar impl param.var))[index]? = some type) :
    ((lowerContextAt module ctx impl).valueTypes (lower module))[index]? = some (some type) := by
  rw [lowerContext_valueTypes_of_accepted accepted implementationRow]
  exact cfg_impl_entry_type_prefix module impl index type
    (entryReplayState_parameter_type (lowerEnv module impl.vars impl.results.toList) row)

theorem accepted_context_provenance_seed {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} {upper : Prov}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (slots : upper.slots = typedContextSlotUpper module ctx impl)
    (retained : ∀ index, index < impl.params.size → rootsAt upper.vals index =
      rootsAt (entryRootValues (impl.params.toList.map fun param => .data (tyOfVar impl param.var))) index) :
    ProvenanceBelow (provStart ((lowerContextAt module ctx impl).valueTypes (lower module))
      (lowerContextAt module ctx impl)) upper := by
  obtain ⟨checkedImpl, row, checked⟩ := (validate_modOk module accepted).ctx context ctx contextRow
  rw [implementationRow] at row
  cases row
  apply provStart_below_retained_entry (types := impl.params.toList.map fun param => .data (tyOfVar impl param.var))
    (by rw [slots]; exact lowerContext_slotRootSeeds_below checked.annotationShape)
  · intro block row
    simpa only [List.length_map, Array.length_toList] using cfg_impl_entry_parameters module impl block row
  · exact fun index type row => accepted_context_entry_type accepted implementationRow row
  · simpa only [List.length_map, Array.length_toList] using retained

#print axioms accepted_context_entry_type
#print axioms accepted_context_provenance_seed

end Goose.Lower.Validation.SummaryPreservation
