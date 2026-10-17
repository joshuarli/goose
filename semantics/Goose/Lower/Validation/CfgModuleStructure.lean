import Goose.Lower.Validation.CfgFunctionCompletion
import Goose.Lower.Validation.CfgFunctionEntry
import Goose.Lower.Validation.CfgFunctionPaths

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure CfgStructure (func : Func) : Prop where
  terminators : ∀ block ∈ func.blocks.toList,
    block.terms.length = 1 ∧ block.lastTerm?.isSome = true
  entry : NoEntryTargets func
  paths : ∀ block, block < func.blocks.size → BlockReachable func block

theorem CfgStructure.reachable {func : Func} (facts : CfgStructure func) :
    ∀ block, block < func.blocks.size → (reachable func)[block]? = some true :=
  fun block bound => reachable_marks_path (Nat.zero_lt_of_lt bound) (facts.paths block bound)

theorem CfgStructure.predecessors_entry {func : Func} (facts : CfgStructure func) :
    (predecessors func)[0]?.getD [] = [] := Goose.Lower.Validation.predecessors_entry func facts.entry

theorem lowerImpl_cfgStructure (module : Core.Module) (impl : Core.Impl) :
    CfgStructure (lowerImpl module impl) :=
  ⟨lowerImpl_terminators module impl, lowerImpl_noEntryTargets module impl, lowerImpl_paths module impl⟩

theorem lowerContextAt_cfgStructure (module : Core.Module) (context : Core.Context) (impl : Core.Impl) :
    CfgStructure (lowerContextAt module context impl) :=
  ⟨lowerContextAt_terminators module context impl, lowerContextAt_noEntryTargets module context impl,
    lowerContextAt_paths module context impl⟩

theorem lowerGlobal_cfgStructure (module : Core.Module) (global : Core.Global) :
    CfgStructure (lowerGlobal module global).init :=
  ⟨lowerGlobal_terminators module global, lowerGlobal_noEntryTargets module global, lowerGlobal_paths module global⟩

theorem invalidContextFunction_cfgStructure (context : Core.Context) : CfgStructure (invalidContextFunction context) := by
  constructor
  · simp [invalidContextFunction]
  · simp [NoEntryTargets, invalidContextFunction]
  · simp [invalidContextFunction]

theorem lower_cfgStructure (module : Core.Module) (func : Func)
    (member : func ∈ (lower module).funcs.toList ++ (lower module).globals.toList.map (·.init)) :
    CfgStructure func := by
  rcases List.mem_append.mp member with implementation | initializer
  · change func ∈ (module.contexts.map fun context =>
        match (module.impls.map fun impl => (impl, lowerImpl module impl))[context.impl]? with
        | some (impl, body) => { body with roots := lowerContextRootInfo context impl }
        | none => invalidContextFunction context).toList at implementation
    simp only [Array.toList_map, List.mem_map] at implementation
    obtain ⟨context, _, equality⟩ := implementation
    rw [Array.getElem?_map] at equality
    cases source : module.impls[context.impl]? with
    | none =>
      simp only [source, Option.map_none] at equality
      subst func
      exact invalidContextFunction_cfgStructure context
    | some impl =>
      simp only [source, Option.map_some] at equality
      subst func
      exact lowerContextAt_cfgStructure module context impl
  · obtain ⟨global, globalMember, rfl⟩ := List.mem_map.mp initializer
    change global ∈ (module.globals.map (lowerGlobal module)).toList at globalMember
    simp only [Array.toList_map, List.mem_map] at globalMember
    obtain ⟨source, _, rfl⟩ := globalMember
    exact lowerGlobal_cfgStructure module source

end Goose.Lower.Validation
