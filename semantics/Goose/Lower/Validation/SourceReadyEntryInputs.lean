import Goose.Lower.Validation.ReplacementContentFlowSourceReadySeedsExtends
import Goose.Lower.Validation.SummaryPreservationEntryBindingFacts
import Goose.Lower.Validation.SummaryPreservationReplayFunctionFinish
import Goose.Lower.Validation.ValidationTypedModuleTables
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes
import Goose.Lower.Finish

namespace Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyEntryInputs

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

private theorem initial_parameter_ready {module : Core.Module} {ctx : Context} {impl : Impl}
    {entry : GIR.Block} {index value : Nat} {type : VTy}
    (entryRow : (lowerContextAt module ctx impl).blocks[0]? = some entry)
    (parameter : entry.params[index]? = some (value, type)) :
    flowAt (start (lowerContextAt module ctx impl)
      ((lowerContextAt module ctx impl).valueTypes (lower module))).values value ≠ .pending := by
  have member := Array.mem_toList_iff.mpr (Array.mem_of_getElem? entryRow)
  have parameterMember := List.mem_of_getElem? parameter
  have dense : (((lowerContextAt module ctx impl).blocks.toList.flatMap GIR.Block.defs).Perm
      (List.range (lowerContextAt module ctx impl).numValues)) := lowerImpl_dense_definitions module impl
  have initial := start_parameter ((lowerContextAt module ctx impl).valueTypes (lower module))
    entryRow (Func.parameter_ids_distinct_of_dense dense member) index value type parameter
    (Func.parameter_ids_bounded_of_dense dense entry member _ parameterMember)
  rw [initial]
  split <;> simp

theorem context_pre_ready {module : Core.Module} {context : ContextId} {ctx : Context} {impl : Impl}
    {state : State}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (growth : (start (lowerContextAt module ctx impl)
      ((lowerContextAt module ctx impl).valueTypes (lower module))).Extends state) :
    ∀ slot input origin,
      (slot, input, origin) ∈ contextEntryBindings impl (lowerEnv module impl.vars impl.results.toList) →
      flowAt state.values input ≠ .pending := by
  intro slot input origin member
  obtain ⟨⟨parameter, value⟩, paired, binding⟩ := List.mem_map.mp member
  obtain ⟨index, localVar, parameterRow, identity, same, variableRow, _⟩ :=
    entry_parameter_pair (lowerEnv module impl.vars impl.results.toList) accepted implementationRow paired
  have inputIndex : input = index :=
    (congrArg (fun binding : SlotId × ValueId × OriginId => binding.2.1) binding).symm.trans same
  rw [inputIndex]
  obtain ⟨entry, entryRow, _⟩ :=
    accepted_context_parameter_slotInit_member accepted contextRow implementationRow parameterRow
  have entryParameters := cfg_impl_entry_parameters module impl entry entryRow
  have parameterAt : impl.params.toList[index]? = some parameter := by
    simpa only [Array.getElem?_toList] using parameterRow
  have entryParameter : entry.params[index]? = some (index, .data localVar.ty) := by
    rw [entryParameters]
    have typeAt : (impl.params.toList.map fun parameter =>
        VTy.data (tyOfVar impl parameter.var))[index]? = some (.data localVar.ty) := by
      simp [parameterAt, identity, variableRow, tyOfVar]
    have indexBound := (Array.getElem?_eq_some_iff.mp parameterRow).1
    simpa only [List.getElem?_zip_eq_some] using ⟨List.getElem?_range indexBound, typeAt⟩
  exact (growth.values.values index).ready (initial_parameter_ready entryRow entryParameter)

theorem context {module : Core.Module} {context : ContextId} {ctx : Context} {impl : Impl}
    {states : Array State} {state : State}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (growth : (start (lowerContextAt module ctx impl)
      ((lowerContextAt module ctx impl).valueTypes (lower module))).Extends state)
    (fixed : round (lower module) states (lowerContextAt module ctx impl)
      ((lowerContextAt module ctx impl).valueTypes (lower module)) state = state) :
    let le := lowerEnv module impl.vars impl.results.toList
    let entry := entryReplayState (impl.params.toList.map fun parameter => .data (tyOfVar impl parameter.var)) le
    let pre := contextEntryBindings impl le
    let body := lowerBlock none pre impl.body.value.isSome impl.body le entry
    ∃ type finish, Core.tyBlock (implEnv module impl) [] impl.body impl.params.size = .ok (type, finish) ∧
      GeneratedBuilderState entry ∧
      NativeRows ((lowerContextAt module ctx impl).valueTypes (lower module)) body.2 ∧
      body.2.Ext (cfg_implState module impl) ∧ body.2.vals.size ≤ (cfg_implState module impl).vals.size ∧
      VisibleSlotsReady (implEnv module impl) state ∧
      (∀ slot input origin, (slot, input, origin) ∈ pre → slot < (lowerContextAt module ctx impl).slots.size) ∧
      (∀ slot input origin, (slot, input, origin) ∈ pre → flowAt state.values input ≠ .pending) := by
  let le := lowerEnv module impl.vars impl.results.toList
  let parameterTypes := impl.params.toList.map fun parameter => VTy.data (tyOfVar impl parameter.var)
  let entry := entryReplayState parameterTypes le
  let pre := contextEntryBindings impl le
  let body := lowerBlock none pre impl.body.value.isSome impl.body le entry
  have whole : cfg_implState module impl = (Goose.Lower.finishFunction impl body.1 le body.2).2 := by
    simp only [cfg_implState, cfg_implAction, bind_run, setCur_run, body, pre, contextEntryBindings,
      entry, entryReplayState, parameterTypes, le, lowerBlock_value_want]
  have nativeFinal : NativeRows ((lowerContextAt module ctx impl).valueTypes (lower module))
      (cfg_implState module impl) := by
    rw [lowerContext_valueTypes_of_accepted accepted implementationRow]
    exact NativeRows.refl _
  have nativeBody : NativeRows ((lowerContextAt module ctx impl).valueTypes (lower module)) body.2 := by
    rw [whole] at nativeFinal
    exact nativeFinal.of_prefix (ReplayBuilder.types_finishFunction impl body.1 le body.2 _ _ rfl)
  have advance : body.2.Adv (cfg_implState module impl) := by
    rw [whole]
    exact advB_finishFunction impl body.1 le body.2 _ _ rfl
  obtain ⟨type, finish, checked, _⟩ :=
    (validate_modOk module accepted).impl ctx.impl impl implementationRow |>.body
  refine ⟨type, finish, checked, entryReplayState_generated parameterTypes le, nativeBody,
    advance.ext, advance.vals,
    accepted_context_visible_slots_ready_of_initial_extends accepted contextRow implementationRow growth fixed,
    ?_, context_pre_ready accepted contextRow implementationRow growth⟩
  intro slot input origin member
  have bounded := (contextEntryBindings_metadata le accepted implementationRow (slot, input, origin) member).1
  simpa only [lowerContextAt, lowerImpl, lowerImplFromState, lowerEnv, Array.size_map, Array.size_mapIdx] using bounded

theorem global {module : Core.Module} {index : GlobalId} {global : Core.Global} {state : State}
    (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global) :
    let le := lowerEnv module #[] [global.ty]
    let entry := entryReplayState [] le
    let initialized := lowerExpr global.init le entry
    ∃ finish, Core.tyExpr (initEnv module index) global.init 0 = .ok (global.ty, finish) ∧
      GeneratedBuilderState entry ∧
      NativeRows ((lowerGlobal module global).init.valueTypes (lower module)) initialized.2 ∧
      initialized.2.Ext (cfg_globalState module global) ∧
      initialized.2.vals.size ≤ (cfg_globalState module global).vals.size ∧
      VisibleSlotsReady (initEnv module index) state := by
  let le := lowerEnv module #[] [global.ty]
  let entry := entryReplayState [] le
  let initialized := lowerExpr global.init le entry
  have whole : cfg_globalState module global =
      (emitTerm (.ret [initialized.1] (some global.org)) le initialized.2).2 := by
    simp only [cfg_globalState, cfg_globalAction, bind_run, setCur_run, initialized, entry,
      entryReplayState, le]
  have nativeFinal : NativeRows ((lowerGlobal module global).init.valueTypes (lower module))
      (cfg_globalState module global) := by
    rw [lowerGlobal_valueTypes_of_accepted accepted globalRow]
    exact NativeRows.refl _
  have nativeValue : NativeRows ((lowerGlobal module global).init.valueTypes (lower module)) initialized.2 := by
    rw [whole] at nativeFinal
    exact nativeFinal.of_prefix (types_emitTerm (.ret [initialized.1] (some global.org)) le initialized.2 _ _ rfl)
  have advance : initialized.2.Adv (cfg_globalState module global) := by
    rw [whole]
    exact advB_emitTerm (.ret [initialized.1] (some global.org)) le initialized.2 _ _ rfl
  obtain ⟨finish, checked⟩ := (validate_modOk module accepted).glob index global globalRow |>.init
  refine ⟨finish, checked, entryReplayState_generated [] le, nativeValue, advance.ext, advance.vals, ?_⟩
  apply VisibleSlotsReady.empty
  rfl

#print axioms context_pre_ready
#print axioms context
#print axioms global

end Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyEntryInputs
