import Goose.Lower.Validation.SourceValueTypeShapesFunctions

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem lower_valueTypeShapes_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (func : Func)
    (member : func ∈ (lower module).funcs.toList ++ (lower module).globals.toList.map (·.init)) :
    ValueTypeShapes (func.valueTypes (lower module)) := by
  rcases List.mem_append.mp member with implementation | initializer
  · change func ∈ (module.contexts.map fun context =>
        match (module.impls.map fun impl => (impl, lowerImpl module impl))[context.impl]? with
        | some (impl, body) => { body with roots := lowerContextRootInfo context impl }
        | none => invalidContextFunction context).toList at implementation
    simp only [Array.toList_map, List.mem_map] at implementation
    obtain ⟨context, contextMember, equality⟩ := implementation
    obtain ⟨index, contextRow⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp contextMember)
    obtain ⟨impl, implRow, _⟩ := (validate_modOk module accepted).ctx index context contextRow
    rw [Array.getElem?_map, implRow] at equality
    simp only [Option.map_some] at equality
    subst func
    exact lowerContext_valueTypeShapes_of_accepted accepted implRow
  · obtain ⟨global, globalMember, rfl⟩ := List.mem_map.mp initializer
    change global ∈ (module.globals.map (lowerGlobal module)).toList at globalMember
    simp only [Array.toList_map, List.mem_map] at globalMember
    obtain ⟨source, sourceMember, rfl⟩ := globalMember
    obtain ⟨index, sourceRow⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp sourceMember)
    exact lowerGlobal_valueTypeShapes_of_accepted accepted sourceRow


#print axioms lower_valueTypeShapes_of_accepted

end Goose.Lower.Validation
