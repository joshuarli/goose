import Goose.Lower.Validation.SourceSymbolSourceEntry
import Goose.Lower.ContextLowering
import Goose.Lower.Validation.OperandFunctions
import Goose.Lower.GeneratedTargetsFunctions
import Goose.Lower.Validation.SymbolSourceTables

namespace Goose.Lower.Validation.SourceSymbolSource

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem instruction_target_member {block : GIR.Block} {inst : Inst}
    (member : inst ∈ block.insts) {target : BlockId} (used : target ∈ instTargetRefs inst) :
    target ∈ block.terms.flatMap Term.successors := by
  cases inst with
  | «def» value op => simp [instTargetRefs] at used
  | eff effect => simp [instTargetRefs] at used
  | term term =>
    apply List.mem_flatMap.mpr
    refine ⟨term, ?_, used⟩
    apply List.mem_filterMap.mpr
    exact ⟨.term term, member, rfl⟩

theorem lowerContextAt_instruction_symbols {module : Core.Module}
    {context : Core.Context} {impl : Impl} (accepted : Core.validate module = .ok ())
    (implAt : module.impls[context.impl]? = some impl) :
    ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ inst ∈ block.insts,
      Inst.SymbolsWithin (lowerEnv module impl.vars impl.results.toList)
        (lowerContextAt module context impl).scopes.size
        (lowerContextAt module context impl).numValues
        (lowerContextAt module context impl).blocks.size inst := by
  intro block blockMember inst instMember
  apply Inst.SymbolsWithin.ofSource
    (lowerContextAt_source_symbols accepted implAt context block blockMember inst instMember)
  · exact (lowerContextAt_operand_bounds module context impl).1 block blockMember inst instMember
  · obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp blockMember)
    intro target used
    exact lowerImpl_targetsBounded module impl row target (instruction_target_member instMember used)

theorem lowerGlobal_instruction_symbols {module : Core.Module} {index : GlobalId}
    {global : Core.Global} (accepted : Core.validate module = .ok ())
    (lookup : module.globals[index]? = some global) :
    ∀ block ∈ (lowerGlobal module global).init.blocks.toList, ∀ inst ∈ block.insts,
      Inst.SymbolsWithin (lowerEnv module #[] [global.ty]) (lowerGlobal module global).init.scopes.size
        (lowerGlobal module global).init.numValues (lowerGlobal module global).init.blocks.size inst := by
  intro block blockMember inst instMember
  apply Inst.SymbolsWithin.ofSource
    (lowerGlobal_source_symbols accepted lookup block blockMember inst instMember)
  · exact (lowerGlobal_operand_bounds module global).1 block blockMember inst instMember
  · obtain ⟨position, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp blockMember)
    intro target used
    exact lowerGlobal_targetsBounded module global row target (instruction_target_member instMember used)

theorem lowerContextAt_checkSymbols {module : Core.Module} {contextIndex : ContextId}
    {context : Core.Context} {impl : Impl} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl) (label : String) :
    checkSymbols (lower module) label (lowerContextAt module context impl) = .ok () :=
  lowerContextAt_checkSymbols_of_references accepted contextAt implAt
    (lowerContextAt_instruction_symbols accepted implAt) label

theorem lowerGlobal_checkSymbols {module : Core.Module} {index : GlobalId}
    {global : Core.Global} (accepted : Core.validate module = .ok ())
    (lookup : module.globals[index]? = some global) (label : String) :
    checkSymbols (lower module) label (lowerGlobal module global).init = .ok () :=
  lowerGlobal_checkSymbols_of_references accepted lookup
    (lowerGlobal_instruction_symbols accepted lookup) label

theorem lower_labelled_checkSymbols {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {label : String} {func : Func}
    (member : (label, func) ∈ (lower module).labelled) :
    checkSymbols (lower module) label func = .ok () := by
  simp only [GIR.Module.labelled, List.mem_append, List.mem_map] at member
  rcases member with ⟨function, member, same⟩ | ⟨loweredGlobal, member, same⟩
  · obtain ⟨_, rfl⟩ := Prod.mk.inj same
    obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    cases contextAt : module.contexts[index]? with
    | none => simp [lower, Array.getElem?_map, contextAt] at lookup
    | some context =>
      obtain ⟨impl, implAt, _⟩ := (validate_modOk module accepted).ctx index context contextAt
      have lowered : (lower module).funcs[index]? = some (lowerContextAt module context impl) := by
        exact lower_func_at contextAt implAt
      have equal := Option.some.inj (lowered.symm.trans lookup)
      rw [← equal]
      exact lowerContextAt_checkSymbols accepted contextAt implAt label
  · obtain ⟨_, rfl⟩ := Prod.mk.inj same
    obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    cases globalAt : module.globals[index]? with
    | none => simp [lower, Array.getElem?_map, globalAt] at lookup
    | some global =>
      have equal : lowerGlobal module global = loweredGlobal := by
        simpa [lower, Array.getElem?_map, globalAt] using lookup
      rw [← equal]
      exact lowerGlobal_checkSymbols accepted globalAt label

theorem lower_checkSymbols {module : Core.Module} (accepted : Core.validate module = .ok ()) :
    (checkAll (lower module).labelled fun (label, func) =>
      checkSymbols (lower module) label func) = .ok () := by
  have clean : ∀ entry ∈ (lower module).labelled,
      checkSymbols (lower module) entry.1 entry.2 = .ok () := by
    intro entry member
    exact lower_labelled_checkSymbols accepted member
  generalize (lower module).labelled = entries at clean ⊢
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨label, func⟩ := entry
    simp only [checkAll, clean (label, func) (by simp), bind, Except.bind]
    apply ih
    intro next member
    exact clean next (by simp [member])

end Goose.Lower.Validation.SourceSymbolSource
