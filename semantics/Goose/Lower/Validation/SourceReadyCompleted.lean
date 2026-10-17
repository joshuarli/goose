import Goose.Lower.Validation.SourceReadyInduction
import Goose.Lower.Validation.SourceReadyFinish
import Goose.Lower.Validation.SourceReadyEntryInputs

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

private theorem all_instructions_of_emits {property : Inst → Prop} {before after : LS}
    (prior : ∀ instruction ∈ before.insts, property instruction)
    (emitted : EmitsOnly property before after) :
    ∀ instruction ∈ after.insts, property instruction := by
  intro instruction member
  obtain ⟨body, bodyMember, instructionMember⟩ := List.mem_flatMap.mp member
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp bodyMember)
  by_cases old : index < before.blocks.size
  · let previous := before.blocks[index]
    have previousAt : before.blocks[index]? = some previous := by simp [previous, old]
    obtain ⟨next, nextAt, _, tail, appended, valid⟩ := emitted.old index previous previousAt
    have same : next = body := Option.some.inj (nextAt.symm.trans row)
    subst next
    rw [appended] at instructionMember
    rcases List.mem_append.mp instructionMember with previousMember | fresh
    · exact prior instruction (List.mem_flatMap.mpr
        ⟨previous, Array.mem_toList_iff.mpr (Array.mem_of_getElem? previousAt), previousMember⟩)
    · exact valid instruction fresh
  · exact emitted.fresh index body row (Nat.le_of_not_gt old) instruction instructionMember

theorem SourceReadyFunction.context_completed (facts : SourceReadyFunction)
    {module : Core.Module} {context : Context} {impl : Impl} {index : ContextId}
    (sourceEq : facts.source = ⟨module, impl, context, []⟩)
    (functionEq : facts.func = lowerContextAt module context impl)
    (typesEq : facts.types = (lowerContextAt module context impl).valueTypes (lower module))
    (completedEq : facts.completed = cfg_implState module impl)
    (contextRow : module.contexts[index]? = some context)
    (implementationRow : module.impls[context.impl]? = some impl) :
    SourceReadyBuilder facts.state facts.completed ∧
      ∀ instruction ∈ facts.completed.insts,
        ReadyCallObservations (lower facts.source.mod) facts.func facts.state instruction := by
  have accepted : Core.validate module = .ok () := by simpa only [sourceEq] using facts.accepted
  have growth : (start (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))).Extends facts.state := by
    simpa only [functionEq, typesEq] using facts.growth
  have fixed : round (lower module) facts.callees (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module)) facts.state = facts.state := by
    simpa only [sourceEq, functionEq, typesEq] using facts.frame.fixed
  let le := lowerEnv module impl.vars impl.results.toList
  let parameterTypes := impl.params.toList.map fun parameter => VTy.data (tyOfVar impl parameter.var)
  let entry := entryReplayState parameterTypes le
  let pre := contextEntryBindings impl le
  let body := lowerBlock none pre impl.body.value.isSome impl.body le entry
  obtain ⟨type, finish, checked, generated, native, extension, allocated, visible, slots, inputs⟩ :=
    SourceReadyEntryInputs.context accepted contextRow implementationRow growth fixed
  have tables : SourceRootTables (implEnv module impl) facts.source := by
    rw [sourceEq]
    exact ⟨rfl, rfl⟩
  have bodyReady := source_block_ready impl.body facts (typingEnv := implEnv module impl)
    (results := impl.results.toList) (before := entry) (sourcePre := []) (pre := pre)
    (loop := none) (want := impl.body.value.isSome) tables checked generated trivial
    (by simpa only [typesEq, pre, entry, parameterTypes, le, implEnv] using native)
    (by simpa only [completedEq, pre, entry, parameterTypes, le, implEnv] using extension)
    (by simpa only [completedEq, pre, entry, parameterTypes, le, implEnv] using allocated) (fun _ => visible)
    (by intro _ _ member; cases member) (by simpa only [functionEq] using slots)
    (fun _ => inputs) (by intro _ _ _ _ same; cases same)
  have ending := finishFunction_ready (module := lower facts.source.mod) (func := facts.func)
    impl body.1 le body.2 (fun live present => bodyReady.1.2 present live)
  have whole : facts.completed = (Goose.Lower.finishFunction impl body.1 le body.2).2 := by
    rw [completedEq]
    simp only [cfg_implState, cfg_implAction, bind_run, setCur_run, body, pre, contextEntryBindings,
      entry, entryReplayState, parameterTypes, le, lowerBlock_value_want]
  have empty : entry.insts = [] := entryReplayState_instructions parameterTypes le
  rw [whole]
  constructor
  · apply SourceReadyBuilder.of_emits (before := entry) ?_ (bodyReady.1.1.trans ending.1)
    intro instruction member
    simp only [empty, List.not_mem_nil] at member
  · apply all_instructions_of_emits (before := entry) ?_ (bodyReady.2.trans ending.2)
    intro instruction member
    simp only [empty, List.not_mem_nil] at member

theorem SourceReadyFunction.global_completed (facts : SourceReadyFunction)
    {module : Core.Module} {global : Core.Global} {index : GlobalId}
    (sourceEq : facts.source = ⟨module, initImpl, initContext, []⟩)
    (typesEq : facts.types = (lowerGlobal module global).init.valueTypes (lower module))
    (completedEq : facts.completed = cfg_globalState module global)
    (globalRow : module.globals[index]? = some global) :
    SourceReadyBuilder facts.state facts.completed ∧
      ∀ instruction ∈ facts.completed.insts,
        ReadyCallObservations (lower facts.source.mod) facts.func facts.state instruction := by
  have accepted : Core.validate module = .ok () := by simpa only [sourceEq] using facts.accepted
  let le := lowerEnv module #[] [global.ty]
  let entry := entryReplayState [] le
  let initialized := lowerExpr global.init le entry
  obtain ⟨finish, checked, generated, native, extension, allocated, visible⟩ :=
    SourceReadyEntryInputs.global (state := facts.state) accepted globalRow
  have tables : SourceRootTables (initEnv module index) facts.source := by
    rw [sourceEq]
    exact ⟨rfl, rfl⟩
  have valueReady := source_expression_ready global.init facts (typingEnv := initEnv module index)
    (results := [global.ty]) (before := entry) tables checked generated
    (by simpa only [typesEq, entry, le, initEnv] using native)
    (by simpa only [completedEq, entry, le, initEnv] using extension)
    (by simpa only [completedEq, entry, le, initEnv] using allocated) (fun _ => visible)
  have ending : EmitsOnly (ReadyOperands facts.state) initialized.2
      (emitTerm (.ret [initialized.1] (some global.org)) le initialized.2).2 := by
    apply ready_emitTerm rfl
    intro live value member
    have same : value = initialized.1 := by simpa [Inst.uses, Term.uses] using member
    exact same ▸ valueReady.1.2 live
  have observedEnding := emitsOnly_emitTerm (.ret [initialized.1] (some global.org))
    (ReadyCallObservations.term (lower facts.source.mod) facts.func facts.state _) le initialized.2 _ _ rfl
  have whole : facts.completed = (emitTerm (.ret [initialized.1] (some global.org)) le initialized.2).2 := by
    rw [completedEq]
    simp only [cfg_globalState, cfg_globalAction, bind_run, setCur_run, initialized, entry, entryReplayState, le]
  have empty : entry.insts = [] := entryReplayState_instructions [] le
  rw [whole]
  constructor
  · apply SourceReadyBuilder.of_emits (before := entry) ?_ (valueReady.1.1.trans ending)
    intro instruction member
    simp only [empty, List.not_mem_nil] at member
  · apply all_instructions_of_emits (before := entry) ?_ (valueReady.2.trans observedEnding)
    intro instruction member
    simp only [empty, List.not_mem_nil] at member

#print axioms SourceReadyFunction.context_completed
#print axioms SourceReadyFunction.global_completed

end Goose.Lower.Validation.ReplacementContentFlowSource
