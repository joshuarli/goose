import Goose.Lower.Validation.EmittedMetadataStaticProfileSourceFunctions
import Goose.Lower.ContextLowering

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lower_functionProfile_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (func : Func)
    (member : func ∈ (lower module).funcs.toList ++ (lower module).globals.toList.map (·.init)) :
    EmittedFunctionProfile module.profile func := by
  rcases List.mem_append.mp member with implementation | initializer
  · obtain ⟨index, functionAt⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp implementation)
    cases contextAt : module.contexts[index]? with
    | none => simp [lower, Array.getElem?_map, contextAt] at functionAt
    | some context =>
      obtain ⟨impl, implAt, _⟩ := (validate_modOk module accepted).ctx index context contextAt
      have same : lowerContextAt module context impl = func :=
        Option.some.inj ((lower_func_at contextAt implAt).symm.trans functionAt)
      rw [← same]
      exact lowerContextAt_functionProfile_of_accepted accepted implAt
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
