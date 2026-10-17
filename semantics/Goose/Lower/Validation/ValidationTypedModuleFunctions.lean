import Goose.Lower.Validation.ValidationTypedModuleDefinitions
import Goose.Lower.ContextLowering

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lower_info_source {module : Core.Module} (accepted : Core.validate module = .ok ())
    {info : FnInfo} (member : info ∈ (lower module).infos) :
    info.vt = info.f.valueTypes (lower module) ∧
    ((∃ (contextIndex : Nat) (context : Context) (impl : Core.Impl), module.contexts[contextIndex]? = some context ∧
      module.impls[context.impl]? = some impl ∧ info.f = lowerContextAt module context impl) ∨
     (∃ (globalIndex : Nat) (global : Core.Global), module.globals[globalIndex]? = some global ∧
       info.f = (lowerGlobal module global).init)) := by
  simp only [GIR.Module.infos, List.mem_map] at member
  obtain ⟨⟨label, func⟩, labelled, rfl⟩ := member
  refine ⟨rfl, ?_⟩
  simp only [GIR.Module.labelled, List.mem_append, List.mem_map] at labelled
  rcases labelled with ⟨function, functionMember, same⟩ | ⟨global, globalMember, same⟩
  · obtain ⟨_, rfl⟩ := Prod.mk.inj same
    obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp functionMember)
    cases contextAt : module.contexts[index]? with
    | none => simp [lower, Array.getElem?_map, contextAt] at lookup
    | some context =>
      obtain ⟨impl, implAt, _⟩ := (Core.Sound.validate_modOk module accepted).ctx index context contextAt
      exact Or.inl ⟨index, context, impl, contextAt, implAt,
        Option.some.inj (lookup.symm.trans (lower_func_at contextAt implAt))⟩
  · obtain ⟨_, rfl⟩ := Prod.mk.inj same
    obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp globalMember)
    cases sourceAt : module.globals[index]? with
    | none => simp [lower, Array.getElem?_map, sourceAt] at lookup
    | some source =>
      have equal : global = lowerGlobal module source := by
        simpa only [lower, Array.getElem?_map, sourceAt, Option.map_some, Option.some.injEq] using lookup.symm
      exact Or.inr ⟨index, source, sourceAt, congrArg (·.init) equal⟩

theorem lower_definitions_typed_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {info : FnInfo}
    (member : info ∈ (lower module).infos) {block : GIR.Block}
    (blockMember : block ∈ info.f.blocks.toList) {value : ValueId} {op : Op}
    (instruction : Inst.def value op ∈ block.insts) :
    checkInstTypes info.f { (lower module).tyEnv info.f with vals := info.vt }
      info.vt (.def value op) = .ok () := by
  obtain ⟨tables, source⟩ := lower_info_source accepted member
  rw [tables]
  rcases source with ⟨contextIndex, context, impl, contextAt, implAt, same⟩ |
    ⟨globalIndex, global, globalAt, same⟩
  · rw [same] at blockMember ⊢
    exact lowerContext_definition_typed_of_accepted accepted implAt blockMember instruction
  · rw [same] at blockMember ⊢
    exact lowerGlobal_definition_typed_of_accepted accepted globalAt blockMember instruction

end Goose.Lower.Validation
