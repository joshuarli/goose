import Goose.Lower.Validation.PermissionPreservationParameters
import Goose.Lower.Validation.PermissionInstructionStorageSourceBase

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem newBlock_implementation_preTransfers
    {module : Core.Module} {impl : Core.Impl} {func : Func}
    (slots : func.slots = (lowerEnv module impl.vars impl.results.toList).slots)
    {allocated : LS} {result : BlockId × List ValueId}
    (run : newBlock (impl.params.toList.map fun parameter => VTy.data (tyOfVar impl parameter.var))
      (lowerEnv module impl.vars impl.results.toList) initState = (result, allocated)) :
    ∀ entry ∈ (impl.params.toList.zip result.2).map (fun (parameter, value) =>
        (parameter.var, value, (impl.vars[parameter.var]?.map (fun localVar : LocalVar => localVar.org)).getD 0)),
      ∀ descriptor, func.slots[entry.1]? = some descriptor →
      PermissionTransfer module.profile
        (FreshWritableEvidence (lowerEnv module impl.vars impl.results.toList) 0 allocated)
        (FreshContentsEvidence (lowerEnv module impl.vars impl.results.toList) 0 allocated)
        entry.2.1 descriptor.ty := by
  intro entry member descriptor descriptorRow
  obtain ⟨⟨parameter, value⟩, zipped, rfl⟩ := List.mem_map.mp member
  have declaredType : descriptor.ty = tyOfVar impl parameter.var := by
    rw [slots] at descriptorRow
    cases localRow : impl.vars[parameter.var]? with
    | none => simp [lowerEnv, Array.getElem?_mapIdx, localRow] at descriptorRow
    | some localVar =>
      have same : (⟨localVar.ty, localVar.kind, localVar.scope, parameter.var⟩ : Slot) = descriptor := by
        simpa [lowerEnv, Array.getElem?_mapIdx, localRow] using descriptorRow
      rw [← same]
      simp [tyOfVar, localRow]
  rw [declaredType]
  obtain ⟨index, zippedRow⟩ := List.mem_iff_getElem?.mp zipped
  obtain ⟨parameterRow, valueRow⟩ := List.getElem?_zip_eq_some.mp zippedRow
  have typeRow : (impl.params.toList.map fun parameter => VTy.data (tyOfVar impl parameter.var))[index]? =
      some (VTy.data (tyOfVar impl parameter.var)) := by
    simp [List.getElem?_map, parameterRow]
  have values : result.2 = paramIds
      (impl.params.toList.map fun parameter => VTy.data (tyOfVar impl parameter.var)) #[] := by
    have shape := congrArg Prod.fst run
    rw [newBlock_run_general] at shape
    exact (congrArg Prod.snd shape).symm
  rw [values] at valueRow
  apply newBlock_initial_parameterTransfer module.profile run
  exact List.mem_iff_getElem?.mpr ⟨index, List.getElem?_zip_eq_some.mpr ⟨valueRow, typeRow⟩⟩

#print axioms newBlock_implementation_preTransfers

end Goose.Lower.Validation
