import Goose.Lower.Validation.ReplacementContentFlowSourceReadySeeds

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem accepted_context_visible_slots_ready_of_initial_extends {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {states : Array State} {final : State}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (growth : (start (lowerContextAt module ctx impl)
      ((lowerContextAt module ctx impl).valueTypes (lower module))).Extends final)
    (fixed : round (lower module) states (lowerContextAt module ctx impl)
      ((lowerContextAt module ctx impl).valueTypes (lower module)) final = final) :
    VisibleSlotsReady (Core.Sound.implEnv module impl) final := by
  intro index visible localVar variableRow reference
  change index ∈ List.range impl.params.size at visible
  change impl.vars[index]? = some localVar at variableRow
  have indexBound := List.mem_range.mp visible
  let param := impl.params[index]
  have parameterRow : impl.params[index]? = some param := Array.getElem?_eq_getElem indexBound
  have shape := (Core.Sound.validate_modOk module accepted).impl ctx.impl impl implementationRow
    |>.params index param parameterRow
  obtain ⟨identity, sourceVar, sourceVariableRow, _, _⟩ := shape
  have sameVariable : sourceVar = localVar := Option.some.inj (sourceVariableRow.symm.trans variableRow)
  subst sourceVar
  have entryFacts := accepted_context_parameter_slotInit_member accepted contextRow
    implementationRow parameterRow
  obtain ⟨entry, entryRow, instructionMember⟩ := entryFacts
  let func := lowerContextAt module ctx impl
  let types := func.valueTypes (lower module)
  have blockMember : entry ∈ func.blocks.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_getElem? entryRow)
  have entryParameters := SummaryPreservation.cfg_impl_entry_parameters module impl entry entryRow
  have parameterAt : impl.params.toList[index]? = some param := by
    simpa only [Array.getElem?_toList] using parameterRow
  have entryParameter : entry.params[index]? = some (index, .data localVar.ty) := by
    rw [entryParameters]
    have typeAt : (impl.params.toList.map fun parameter =>
        VTy.data (tyOfVar impl parameter.var))[index]? = some (.data localVar.ty) := by
      simp [parameterAt, identity, variableRow, tyOfVar]
    simpa only [List.getElem?_zip_eq_some] using ⟨List.getElem?_range indexBound, typeAt⟩
  have startValue : flowAt (start func types).values index = .known [.param index] := by
    simpa only [func, types] using
      (accepted_initial_parameter_value (env := ⟨module, impl, ctx, []⟩) accepted contextRow
        implementationRow reference entryRow entryParameter)
  have initialValueReady : flowAt (start func types).values index ≠ .pending := by
    rw [startValue]
    simp
  have valueReady : flowAt final.values index ≠ .pending := by
    exact (growth.values.values index).ready initialValueReady
  have variableBound : index < impl.vars.size := (Array.getElem?_eq_some_iff.mp variableRow).1
  have functionSlotSize : func.slots.size = impl.vars.size := by
    simp [func, lowerContextAt, lowerImpl, lowerEnv]
  have startSlotSize : (start func types).slots.size = func.slots.size := by
    unfold start
    cases func.blocks[0]? <;> simp
  have slotBound : index < final.slots.size := by
    calc
      index < func.slots.size := by rw [functionSlotSize]; exact variableBound
      _ = (start func types).slots.size := startSlotSize.symm
      _ = final.slots.size := growth.slots.size
  exact round_slotInit_ready fixed blockMember instructionMember slotBound valueReady


theorem accepted_context_visible_slots_ready_of_module_close
    {module : Core.Module} {context : ContextId} {ctx : Context} {impl : Impl}
    {states : Array State} {final : State}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (closed : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states)
    (stateRow : states[context]? = some final) :
    VisibleSlotsReady (Core.Sound.implEnv module impl) final := by
  have functionRow := lower_func_at contextRow implementationRow
  have typeRow : ((lower module).funcs.map (·.valueTypes (lower module)))[context]? =
      some ((lowerContextAt module ctx impl).valueTypes (lower module)) := by
    simp only [Array.getElem?_map, functionRow, Option.map_some]
  have growth := (close_initial_extends closed).values context
  have initialRow : (moduleStart (lower module)
      ((lower module).funcs.map (·.valueTypes (lower module))))[context]? =
      some (start (lowerContextAt module ctx impl)
        ((lowerContextAt module ctx impl).valueTypes (lower module))) := by
    simp only [moduleStart, Array.getElem?_mapIdx, functionRow, typeRow, Option.map_some,
      Option.getD_some]
  simp only [initialRow, stateRow, Option.getD_some] at growth
  have fixed := moduleRound_fixed_function (close_fixed closed) context _ _ functionRow stateRow
  simp only [typeRow, Option.getD_some] at fixed
  exact accepted_context_visible_slots_ready_of_initial_extends accepted contextRow implementationRow growth fixed

theorem accepted_module_visible_slots_ready {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    ∃ states, close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states ∧
      ∀ (context : ContextId) (ctx : Context) (impl : Impl),
        module.contexts[context]? = some ctx → module.impls[ctx.impl]? = some impl →
        ∃ final, states[context]? = some final ∧ VisibleSlotsReady (Core.Sound.implEnv module impl) final := by
  obtain ⟨states, closed, _, _⟩ := accepted_module_close_finite accepted
  refine ⟨states, closed, ?_⟩
  intro context ctx impl contextRow implementationRow
  have sizes : module.contexts.size = states.size := by
    simpa only [moduleStart, lower, Array.size_mapIdx, Array.size_map] using
      (close_initial_extends closed).size
  have bound : context < states.size := by
    rw [← sizes]
    exact (Array.getElem?_eq_some_iff.mp contextRow).1
  let final := states[context]
  have stateRow : states[context]? = some final := Array.getElem?_eq_getElem bound
  exact ⟨final, stateRow,
    accepted_context_visible_slots_ready_of_module_close accepted contextRow implementationRow closed stateRow⟩

end Goose.Lower.Validation.ReplacementContentFlowSource
