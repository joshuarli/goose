import Goose.Lower.Validation.EmittedMetadataStaticProfileSourceFunctions

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lower_functionProfile_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (func : Func)
    (member : func ∈ (lower module).funcs.toList ++ (lower module).globals.toList.map (·.init)) :
    EmittedFunctionProfile module.profile func := by
  rcases List.mem_append.mp member with implementation | initializer
  · change func ∈ (module.contexts.map fun context =>
        match (module.impls.map fun impl =>
          (impl, lowerImplFromState module impl (lowerImplState module impl), lowerImplState module impl))[context.impl]? with
        | some (impl, body, state) => { body with roots := { lowerContextRootInfo context impl with
            values := lowerContextValueRoots module context impl state } }
        | none => invalidContextFunction context).toList at implementation
    simp only [Array.toList_map, List.mem_map] at implementation
    obtain ⟨context, contextMember, equality⟩ := implementation
    obtain ⟨index, contextRow⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp contextMember)
    obtain ⟨impl, implRow, _⟩ := (validate_modOk module accepted).ctx index context contextRow
    rw [Array.getElem?_map, implRow] at equality
    simp only [Option.map_some] at equality
    subst func
    exact lowerContextAt_functionProfile_of_accepted accepted implRow
  · obtain ⟨global, globalMember, rfl⟩ := List.mem_map.mp initializer
    change global ∈ (module.globals.map (lowerGlobal module)).toList at globalMember
    simp only [Array.toList_map, List.mem_map] at globalMember
    obtain ⟨source, sourceMember, rfl⟩ := globalMember
    obtain ⟨index, sourceRow⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp sourceMember)
    exact lowerGlobal_functionProfile_of_accepted accepted sourceRow

theorem lower_pilot_excludes_shrink_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (pilot : module.profile = .pilot)
    (func : Func) (member : func ∈ (lower module).funcs.toList ++ (lower module).globals.toList.map (·.init))
    (block : GIR.Block) (atBlock : block ∈ func.blocks.toList) (inst : Inst) (atInst : inst ∈ block.insts) :
    EmittedProfileInst .pilot inst := by
  have checked := lower_functionProfile_of_accepted accepted func member block atBlock inst atInst
  simpa only [pilot] using checked

end Goose.Lower.Validation
