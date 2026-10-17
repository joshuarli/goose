import Goose.Lower.Validation.SourceReadyModuleChecks
import Goose.Lower.Validation.SourceReadyInstructionChecks
import Goose.Lower.Validation.ValidationTypedModuleInstructions
import Goose.Lower.Validation.ValidationTypedModuleEntry

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR Goose.Core.Sound SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFunction.context_check (facts : SourceReadyFunction)
    {module : Core.Module} {context : Context} {impl : Impl} {index : Nat}
    (sourceEq : facts.source = ⟨module, impl, context, []⟩)
    (functionEq : facts.func = lowerContextAt module context impl)
    (typesEq : facts.types = (lowerContextAt module context impl).valueTypes (lower module))
    (provenanceEq : facts.provenance = (lowerContextAt module context impl).provenance
      (GIR.resultRoots (lower module) (lower module).implTypes)
      ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount)
    (completedEq : facts.completed = cfg_implState module impl)
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    (ready : SourceReadyBuilder facts.state facts.completed)
    (observed : ∀ instruction ∈ facts.completed.insts,
      ReadyCallObservations (lower facts.source.mod) facts.func facts.state instruction)
    (assigned : ∀ (index : Nat) (roots : Roots), facts.state.writes[index]? = some (.assigned roots) →
      roots ≠ .pending) :
    check (lower facts.source.mod) facts.func facts.types facts.state = true := by
  have accepted : Core.validate module = .ok () := by simpa only [sourceEq] using facts.accepted
  have retained : facts.types = facts.completed.vals := by
    rw [typesEq, completedEq, lowerContext_valueTypes_of_accepted accepted implAt]
  have emitted := lowerImpl_emittedBuilder_of_accepted accepted implAt
  have present := emitted.present (by intro value bounded; simp [initState] at bounded)
  have allPresent : ∀ value, value < facts.func.numValues → ∃ type, facts.types[value]? = some (some type) := by
    intro value bounded
    rw [retained, completedEq]
    apply present value
    rw [← completedEq, facts.frame.values]
    exact bounded
  have edges : BuilderEdgeArguments facts.completed := by
    rw [completedEq]
    exact lowerImpl_builderEdges_of_accepted accepted implAt
  let func := lowerContextAt module context impl
  let info : FnInfo := ⟨s!"function {func.name}", func, func.valueTypes (lower module)⟩
  have infoMember : info ∈ (lower module).infos := by
    apply List.mem_map.mpr
    refine ⟨(s!"function {func.name}", func), ?_, rfl⟩
    apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨func, Array.mem_toList_iff.mpr (Array.mem_of_getElem? (lower_func_at contextAt implAt)), rfl⟩
  have instructions : ∀ block ∈ facts.func.blocks.toList, ∀ instruction ∈ block.insts,
      checkInstruction (lower facts.source.mod) facts.func facts.types facts.state instruction = true := by
    intro block member instruction instructionMember
    apply facts.check_instruction ready observed allPresent edges retained member instructionMember
    have native := lower_instructions_typed_of_accepted accepted infoMember
      (by simpa only [functionEq, info, func] using member) instructionMember
    simpa only [info, func, sourceEq, functionEq, typesEq] using native
  have parameters : ∀ block ∈ facts.func.blocks.toList, ∀ pair ∈ block.params,
      facts.types[pair.1]? = some (some pair.2) := by
    intro block member pair parameter
    rw [facts.frame.blocks, finishBlocks, Array.toList_map] at member
    obtain ⟨builder, builderMember, same⟩ := List.mem_map.mp member
    obtain ⟨blockId, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp builderMember)
    rw [retained, completedEq]
    apply emitted.checkpoint.parameters blockId builder
      (by simpa only [completedEq] using row) pair.1 pair.2
    simpa only [← same] using parameter
  have paramsCheck : facts.func.params.all Ty.paramOk = true :=
    List.all_eq_true.mpr facts.native.roots.parameters
  have annotationCheck : annotationsValid (lower facts.source.mod) facts.func = true := by
    simpa only [sourceEq, functionEq] using accepted_context_annotationsValid accepted contextAt implAt
  have entryCheck : (facts.func.blocks[0]?).any
      (fun entry => entry.params.map (·.2) == facts.func.params.map VTy.data) = true := by
    obtain ⟨entry, row, typed⟩ := lowerContext_entry_types module context impl
    rw [functionEq, row]
    simp only [Option.any_some, typed, beq_self_eq_true]
  have writesCheck : checkWrites facts.func facts.state = true :=
    checkWrites_of_canonical facts.canonical facts.native.roots.closed facts.native.roots.unique assigned
  have returnedCheck : checkReturned facts.func facts.state = true := by
    rw [functionEq]
    apply accepted_context_checkReturned accepted contextAt implAt
    · simpa only [functionEq, typesEq, provenanceEq] using facts.canonical
    · simpa only [functionEq, typesEq] using facts.growth
  have result : check (lower facts.source.mod) facts.func facts.types facts.state = true := by
    simp only [check, paramsCheck, annotationCheck, entryCheck, writesCheck, returnedCheck, Bool.true_and]
    apply Array.all_eq_true.mpr
    intro blockId bounded
    let block := facts.func.blocks[blockId]
    have inBlocks : block ∈ facts.func.blocks.toList := Array.mem_toList_iff.mpr
      (Array.mem_of_getElem? (Array.getElem?_eq_getElem bounded))
    simp only [Bool.and_eq_true]
    constructor
    · exact List.all_eq_true.mpr (fun pair member => beq_iff_eq.mpr (parameters block inBlocks pair member))
    · exact List.all_eq_true.mpr (instructions block inBlocks)
  exact result

theorem accepted_context_model_check {module : Core.Module} {states : Array State}
    {context : Context} {impl : Impl} {index : Nat} {state : State}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    (closed : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states)
    (stateAt : states[index]? = some state) :
    check (lower module) (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module)) state = true := by
  obtain ⟨facts, sourceEq, rootEq, functionEq, typesEq, provenanceEq, completedEq,
      moduleTypesEq, resultRootsEq, calleesEq, stateEq⟩ :=
    accepted_context_module_ready_inputs accepted contextAt implAt closed stateAt
  obtain ⟨ready, observed⟩ := facts.context_completed sourceEq functionEq typesEq completedEq contextAt implAt
  have assigned : ∀ (parameter : Nat) (roots : Roots), facts.state.writes[parameter]? = some (.assigned roots) →
      roots ≠ .pending := by
    simpa only [stateEq] using (accepted_module_assigned_nonpending accepted closed index
      (lowerContextAt module context impl) state (lower_func_at contextAt implAt) stateAt)
  have result := facts.context_check sourceEq functionEq typesEq provenanceEq completedEq
    contextAt implAt ready observed assigned
  simpa only [sourceEq, functionEq, typesEq, stateEq] using result

theorem accepted_module_model_check {module : Core.Module} {states : Array State}
    (accepted : Core.validate module = .ok ())
    (closed : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states)
    {index : Nat} {func : Func} {state : State}
    (funcAt : (lower module).funcs[index]? = some func) (stateAt : states[index]? = some state) :
    check (lower module) func (func.valueTypes (lower module)) state = true := by
  obtain ⟨context, impl, contextAt, implAt, function⟩ := accepted_function_context accepted funcAt
  rw [function]
  exact accepted_context_model_check accepted contextAt implAt closed stateAt

#print axioms SourceReadyFunction.context_check
#print axioms accepted_context_model_check
#print axioms accepted_module_model_check

end Goose.Lower.Validation.ReplacementContentFlowSource
