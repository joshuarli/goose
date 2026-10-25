import Goose.Lower.Frag
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyCore
import Goose.Lower.Validation.ReplacementContentFlowSourceParameters
import Goose.Lower.Validation.ReplacementContentFlowSourceClosure
import Goose.Lower.Validation.ReplacementContentFlowSourceReadySteps
import Goose.Lower.Validation.SummaryPreservationFunctionEntryFrame
import Goose.Lower.Validation.CfgBuilderFunctions
import Goose.Lower.Finish

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

private theorem advB_lowerBlockAfterInitialSlots (loop : Option LoopCtx) (want : Bool)
    (scope : ScopeId) (statements : List Stmt) (value : Option Expr) :
    AdvB (do
      lowerStmts loop statements
      let result ← lowerBlockValue want value
      emitEffect (.leave scope)
      pure result) := by
  exact AdvB.bind (advB_lowerStmts loop statements) fun _ =>
    AdvB.bind (advB_lowerBlockValue want value) fun _ =>
      AdvB.bind (advB_emitEffect (.leave scope)) fun _ => AdvB.pure _

private theorem initSlots_contains
    {bindings : List (Goose.GIR.SlotId × Goose.GIR.ValueId × Goose.Core.OriginId)}
    {le : Goose.Lower.LEnv} {before after : Goose.Lower.LS}
    {block : Goose.GIR.BlockId} {initialBlock : Goose.Lower.BlockB}
    (run : initSlots bindings le before = ((), after))
    (current : before.cur = some block)
    (initialRow : before.blocks[block]? = some initialBlock) :
    ∀ slot value origin, (slot, value, origin) ∈ bindings →
      ∃ finalBlock, after.blocks[block]? = some finalBlock ∧
        .eff (.slotInit slot value (some origin)) ∈ finalBlock.insts := by
  induction bindings generalizing before after initialBlock with
  | nil =>
    intro slot value origin member
    simp at member
  | cons binding rest ih =>
    rcases binding with ⟨firstSlot, firstValue, firstOrigin⟩
    unfold initSlots at run
    obtain ⟨_, middle, firstRun, tailRun⟩ := bind_eq.mp run
    rw [emitEffect_run (.slotInit firstSlot firstValue (some firstOrigin)) le current] at firstRun
    let firstInst : Inst := .eff (.slotInit firstSlot firstValue (some firstOrigin))
    have middleEq : middle = ({ before with blocks := before.blocks.modify block fun blk => { blk with insts := blk.insts.push firstInst } }) :=
      (congrArg Prod.snd firstRun).symm
    have middleRow : middle.blocks[block]? =
          some { initialBlock with insts := initialBlock.insts.push firstInst } := by
      rw [middleEq]
      simp [initialRow, Array.getElem?_modify]
    have middleCurrent : middle.cur = some block := by
      rw [middleEq]
      exact current
    have firstMember : firstInst ∈ ({ initialBlock with insts := initialBlock.insts.push firstInst }).insts := by
      simp
    have extension := (advB_initSlots rest le _ () after tailRun).ext
    have carry {slot value origin} (member : (slot, value, origin) ∈ rest) :
        ∃ finalBlock, after.blocks[block]? = some finalBlock ∧
          .eff (.slotInit slot value (some origin)) ∈ finalBlock.insts := by
      exact ih tailRun middleCurrent middleRow slot value origin member
    intro slot value origin member
    rcases List.mem_cons.mp member with first | restMember
    · have same : slot = firstSlot ∧ value = firstValue ∧ origin = firstOrigin := by
        simpa only [Prod.mk.injEq] using first
      rcases same with ⟨rfl, rfl, rfl⟩
      obtain ⟨finalBlock, finalRow, _, suffix, insts⟩ := extension.2 block _ middleRow
      refine ⟨finalBlock, finalRow, ?_⟩
      apply Array.mem_toList_iff.mp
      rw [insts]
      exact List.mem_append.mpr (Or.inl (Array.mem_toList_iff.mpr firstMember))
    · exact carry restMember

private theorem lowerBlock_initialSlots_contained {loop : Option LoopCtx} {want : Bool}
    {bindings : List (SlotId × ValueId × OriginId)} {scope : ScopeId}
    {statements : List Stmt} {value : Option Expr} {le : LEnv}
    {before after : LS} {block : BlockId} {initialBlock : BlockB} {result : ValueId}
    (run : lowerBlock loop bindings want (.mk scope statements value) le before = (result, after))
    (current : before.cur = some block)
    (initialRow : before.blocks[block]? = some initialBlock) :
    ∀ slot input origin, (slot, input, origin) ∈ bindings →
      ∃ finalBlock, after.blocks[block]? = some finalBlock ∧
        .eff (.slotInit slot input (some origin)) ∈ finalBlock.insts := by
  unfold lowerBlock at run
  obtain ⟨_, entered, enterRun, scopedRun⟩ := bind_eq.mp run
  rw [emitEffect_run (.enter scope) le current] at enterRun
  have enteredEq : entered = ({ before with blocks := Array.modify before.blocks block (fun blk => { blk with insts := blk.insts.push (.eff (.enter scope)) }) }) :=
    (congrArg Prod.snd enterRun).symm
  have enteredRow : entered.blocks[block]? =
      some { initialBlock with insts := initialBlock.insts.push (.eff (.enter scope)) } := by
    rw [enteredEq]
    simp [initialRow, Array.getElem?_modify]
  have enteredCurrent : entered.cur = some block := by
    rw [enteredEq]
    exact current
  obtain ⟨scopedBody, bodyRun, afterScope⟩ := inScope_eq scopedRun
  let scopedStart : LS := { entered with stack := scope :: entered.stack }
  have scopedStartRow : scopedStart.blocks[block]? =
      some { initialBlock with insts := initialBlock.insts.push (.eff (.enter scope)) } := by
    simpa [scopedStart] using enteredRow
  have scopedStartCurrent : scopedStart.cur = some block := by
    simpa [scopedStart] using enteredCurrent
  obtain ⟨_, afterInitialSlots, initializeRun, suffixRun⟩ := bind_eq.mp bodyRun
  have suffixAdvance := advB_lowerBlockAfterInitialSlots loop want scope statements value le
    afterInitialSlots _ scopedBody suffixRun
  have scopeExtension : scopedBody.Ext after := by
    rw [afterScope]
    exact LS.Ext.refl _
  have finalExtension := suffixAdvance.ext.trans scopeExtension
  intro slot input origin member
  obtain ⟨middleBlock, middleRow, middleMember⟩ :=
    initSlots_contains initializeRun scopedStartCurrent scopedStartRow slot input origin member
  obtain ⟨finalBlock, finalRow, _, suffix, insts⟩ := finalExtension.2 block middleBlock middleRow
  refine ⟨finalBlock, finalRow, ?_⟩
  apply Array.mem_toList_iff.mp
  rw [insts]
  exact List.mem_append.mpr (Or.inl (Array.mem_toList_iff.mpr middleMember))

theorem accepted_context_parameter_slotInit_member {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {index : Nat} {param : Param}
    (accepted : Core.validate module = .ok ())
    (_contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (parameterRow : impl.params[index]? = some param) :
    ∃ entry, (lowerContextAt module ctx impl).blocks[0]? = some entry ∧
      Inst.eff (.slotInit index index (some ((impl.vars[index]?.map (·.org)).getD 0))) ∈ entry.insts := by
  have parameterShape := (Core.Sound.validate_modOk module accepted).impl ctx.impl impl implementationRow
    |>.params index param parameterRow
  obtain ⟨identity, _⟩ := parameterShape
  let le := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun parameter => VTy.data (tyOfVar impl parameter.var)
  let entry := SummaryPreservation.entryReplayState types le
  let bindings := (impl.params.toList.zip
    (newBlock (impl.params.toList.map fun parameter => VTy.data (tyOfVar impl parameter.var)) le initState).1.2).map
      fun (parameter, value) =>
        (parameter.var, value,
          (impl.vars[parameter.var]?.map fun localVar : LocalVar => localVar.org).getD 0)
  let body := lowerBlock none bindings false impl.body
  let bodyState := body le entry
  have bodyRun : lowerBlock none bindings false impl.body le entry =
      (bodyState.1, bodyState.2) := rfl
  have whole : cfg_implState module impl = (finishFunction impl bodyState.1 le bodyState.2).2 := by
    simp only [cfg_implState, cfg_implAction, bind_run, setCur_run, bodyState, body, bindings,
      entry, SummaryPreservation.entryReplayState, types, le]
  let initialBlock : BlockB := ⟨(List.range types.length).zip types, #[]⟩
  have initialRow : entry.blocks[0]? = some initialBlock := by
    simp [entry, SummaryPreservation.entryReplayState, initialBlock, newBlock_run_general,
      initState, types, paramIds]
  have entryCurrent : entry.cur = some 0 := by
    simp [entry, SummaryPreservation.entryReplayState, newBlock_run_general, initState]
  have parameterAt : impl.params.toList[index]? = some param := by
    simpa only [Array.getElem?_toList] using parameterRow
  have parameterBound : index < impl.params.size := (Array.getElem?_eq_some_iff.mp parameterRow).1
  have indexAt : (List.range impl.params.size)[index]? = some index := List.getElem?_range parameterBound
  have values : (newBlock (impl.params.toList.map fun parameter => VTy.data (tyOfVar impl parameter.var)) le initState).1.2 =
      List.range impl.params.size := by
    simp [newBlock_run_general, paramIds, initState]
  have valueAt :
      (newBlock (impl.params.toList.map fun parameter => VTy.data (tyOfVar impl parameter.var)) le initState).1.2[index]? = some index := by
    rw [values]
    exact indexAt
  have pairAt : (impl.params.toList.zip
      (newBlock (impl.params.toList.map fun parameter => VTy.data (tyOfVar impl parameter.var)) le initState).1.2)[index]? =
      some (param, index) := List.getElem?_zip_eq_some.mpr ⟨parameterAt, valueAt⟩
  have pairMember := List.mem_of_getElem? pairAt
  let origin := (impl.vars[index]?.map (·.org)).getD 0
  have bindingMember : (index, index, origin) ∈ bindings := by
    apply List.mem_map.mpr
    refine ⟨(param, index), pairMember, ?_⟩
    change (param.var, index, (impl.vars[param.var]?.map (·.org)).getD 0) =
      (index, index, (impl.vars[index]?.map (·.org)).getD 0)
    rw [identity]
  have emitted := by
    cases bodyEq : impl.body with
    | mk scope statements value =>
      exact lowerBlock_initialSlots_contained (by simpa [bodyEq] using bodyRun)
        entryCurrent initialRow index index origin bindingMember
  obtain ⟨bodyBlock, bodyRow, bodyMember⟩ := emitted
  let finished := (finishFunction impl bodyState.1 le bodyState.2).2
  have finishedExtension : bodyState.2.Ext finished :=
    (advB_finishFunction impl bodyState.1 le bodyState.2 () finished rfl).ext
  obtain ⟨finishedBlock, finishedRow, _, suffix, blockInsts⟩ :=
    finishedExtension.2 0 bodyBlock bodyRow
  have finishedMember : Inst.eff
      (.slotInit index index (some ((impl.vars[index]?.map (·.org)).getD 0))) ∈ finishedBlock.insts := by
    apply Array.mem_toList_iff.mp
    rw [blockInsts]
    exact List.mem_append.mpr (Or.inl (Array.mem_toList_iff.mpr bodyMember))
  let output : GIR.Block := ⟨finishedBlock.params, finishedBlock.insts.toList⟩
  have outputRow : (lowerContextAt module ctx impl).blocks[0]? = some output := by
    rw [cfg_context_blocks, whole]
    simp [output, finished, finishBlocks, Array.getElem?_map, finishedRow]
  refine ⟨output, outputRow, ?_⟩
  exact Array.mem_toList_iff.mpr finishedMember

theorem accepted_context_visible_slots_ready {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {states : Array State} {final : State}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (reachable : FunctionReachable (lower module) states (lowerContextAt module ctx impl)
      ((lowerContextAt module ctx impl).valueTypes (lower module))
      (start (lowerContextAt module ctx impl)
        ((lowerContextAt module ctx impl).valueTypes (lower module))) final)
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
  have growth := reachable.extends
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

theorem accepted_context_parameter_initial_normalized {module : Core.Module}
    {context : ContextId} {ctx : Context} {impl : Impl} {index : Nat} {param : Param}
    {localVar : LocalVar} {entry : GIR.Block}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (parameterRow : impl.params[index]? = some param)
    (variableRow : impl.vars[param.var]? = some localVar)
    (reference : localVar.ty.isRefLike = true)
    (entryRow : (lowerContextAt module ctx impl).blocks[0]? = some entry)
    (entryParameter : entry.params[index]? = some (index, .data localVar.ty)) :
    normalize (lowerContextAt module ctx impl)
      (flowAt (start (lowerContextAt module ctx impl)
        ((lowerContextAt module ctx impl).valueTypes (lower module))).values index) =
      some (unionRoots [] ((lowerContextAt module ctx impl).parameterRoots index)) := by
  have identity := ((Core.Sound.validate_modOk module accepted).impl ctx.impl impl implementationRow)
    |>.params index param parameterRow |>.1
  have variableAt : impl.vars[index]? = some localVar := by simpa [identity] using variableRow
  have startValue := accepted_initial_parameter_value
    (env := ⟨module, impl, ctx, []⟩) accepted contextRow implementationRow reference entryRow entryParameter
  rw [startValue]
  exact normalize_parameter _ index

theorem accepted_entry_initial_seed {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    ∃ ctx impl, module.contexts[module.entry]? = some ctx ∧
      module.impls[ctx.impl]? = some impl ∧ impl.params.size = 0 ∧
      VisibleSlotsReady (Core.Sound.implEnv module impl)
        (start (lowerContextAt module ctx impl)
          ((lowerContextAt module ctx impl).valueTypes (lower module))) ∧
      normalize (lowerContextAt module ctx impl)
        (start (lowerContextAt module ctx impl)
          ((lowerContextAt module ctx impl).valueTypes (lower module))).returned = some [] := by
  obtain ⟨ctx, impl, contextRow, implementationRow, parameters, _⟩ :=
    (Core.Sound.validate_modOk module accepted).entry
  refine ⟨ctx, impl, contextRow, implementationRow, parameters, ?_, ?_⟩
  · apply VisibleSlotsReady.empty
    simp [Core.Sound.implEnv, parameters]
  · rw [start_returned]
    exact normalize_empty _

theorem accepted_global_initializer_start_seed {module : Core.Module}
    {index : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global) :
    Core.Sound.GlobOk module index global ∧
    VisibleSlotsReady (Core.Sound.initEnv module index)
      (start (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))) ∧
    normalize (lowerGlobal module global).init
      (start (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))).returned = some [] := by
  refine ⟨(Core.Sound.validate_modOk module accepted).glob index global globalRow, ?_⟩
  constructor
  · apply VisibleSlotsReady.empty
    rfl
  · rw [start_returned]
    exact normalize_empty _

#print axioms accepted_context_visible_slots_ready
#print axioms accepted_context_parameter_initial_normalized
#print axioms accepted_entry_initial_seed
#print axioms accepted_global_initializer_start_seed

end Goose.Lower.Validation.ReplacementContentFlowSource
