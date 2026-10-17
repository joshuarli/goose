import Goose.Lower.Validation.SourceReadyModuleCheck
import Goose.Lower.Validation.SourceReadyLocalWrites

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR Goose.Core.Sound SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFunction.global_check (facts : SourceReadyFunction)
    {module : Core.Module} {global : Core.Global} {index : Nat}
    (sourceEq : facts.source = ⟨module, initImpl, initContext, []⟩)
    (functionEq : facts.func = (lowerGlobal module global).init)
    (typesEq : facts.types = (lowerGlobal module global).init.valueTypes (lower module))
    (completedEq : facts.completed = cfg_globalState module global)
    (globalAt : module.globals[index]? = some global)
    (ready : SourceReadyBuilder facts.state facts.completed)
    (observed : ∀ instruction ∈ facts.completed.insts,
      ReadyCallObservations (lower facts.source.mod) facts.func facts.state instruction)
    (assigned : ∀ (index : Nat) (roots : Roots), facts.state.writes[index]? = some (.assigned roots) →
      roots ≠ .pending) :
    check (lower facts.source.mod) facts.func facts.types facts.state = true := by
  have accepted : Core.validate module = .ok () := by simpa only [sourceEq] using facts.accepted
  have retained : facts.types = facts.completed.vals := by
    rw [typesEq, completedEq, lowerGlobal_valueTypes_of_accepted accepted globalAt]
  have emitted := lowerGlobal_emittedBuilder_of_accepted accepted globalAt
  have present := emitted.present (by intro value bounded; simp [initState] at bounded)
  have allPresent : ∀ value, value < facts.func.numValues → ∃ type, facts.types[value]? = some (some type) := by
    intro value bounded
    rw [retained, completedEq]
    apply present value
    rw [← completedEq, facts.frame.values]
    exact bounded
  have edges : BuilderEdgeArguments facts.completed := by
    rw [completedEq]
    exact lowerGlobal_builderEdges_of_accepted accepted globalAt
  let func := (lowerGlobal module global).init
  let info : FnInfo := ⟨s!"initializer of global {global.name}", func, func.valueTypes (lower module)⟩
  have globalRow : (lower module).globals[index]? = some (lowerGlobal module global) := by
    simp only [lower, Array.getElem?_map, globalAt, Option.map_some]
  have infoMember : info ∈ (lower module).infos := by
    apply List.mem_map.mpr
    refine ⟨(s!"initializer of global {global.name}", func), ?_, rfl⟩
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨lowerGlobal module global, Array.mem_toList_iff.mpr (Array.mem_of_getElem? globalRow), rfl⟩
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
    simpa only [sourceEq, functionEq] using accepted_global_annotationsValid accepted globalAt
  have entryCheck : (facts.func.blocks[0]?).any
      (fun entry => entry.params.map (·.2) == facts.func.params.map VTy.data) = true := by
    obtain ⟨entry, row, typed⟩ := lowerGlobal_entry_types module global
    rw [functionEq, row]
    simp only [Option.any_some, typed, beq_self_eq_true]
  have writesCheck : checkWrites facts.func facts.state = true :=
    checkWrites_of_canonical facts.canonical facts.native.roots.closed facts.native.roots.unique assigned
  have returnedCheck : checkReturned facts.func facts.state = true := by
    apply checkReturned_of_initial_extends facts.canonical facts.native.roots.closed facts.growth
    · exact Or.inr ⟨global.ty, by rw [functionEq]; rfl⟩
    · intro type single reference
      have size := (lowerGlobal_symbol_tables accepted globalAt).resultRows
      have bound : 0 < facts.func.roots.results.size := by
        rw [functionEq, size]
        change 0 < [global.ty].length
        simp only [List.length_singleton, Nat.zero_lt_succ]
      exact ⟨_, Array.getElem?_eq_getElem bound⟩
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

theorem accepted_global_closeFunction {module : Core.Module} {states : Array State}
    {global : Core.Global} {index : Nat}
    (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[index]? = some global)
    (closed : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states) :
    ∃ state, closeFunction (lower module) states (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module)) = some state := by
  obtain ⟨facts, sourceEq, rootEq, functionEq, typesEq, provenanceEq, completedEq,
      moduleTypesEq, resultRootsEq, reachable, outcome⟩ :=
    accepted_global_ready_inputs accepted globalAt
  have modelTypes : facts.moduleTypes =
      (lower facts.source.mod).funcs.map (·.valueTypes (lower facts.source.mod)) := by
    simpa only [sourceEq] using moduleTypesEq
  have sameClosure : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) =
      some facts.callees := by
    simpa only [sourceEq, moduleTypesEq] using facts.closed
  have calleesEq : facts.callees = states := Option.some.inj (sameClosure.symm.trans closed)
  have path : FunctionReachable (lower facts.source.mod) facts.callees facts.func facts.types
      (start facts.func facts.types) facts.state := by simpa only [sourceEq] using reachable
  obtain ⟨ready, observed⟩ := facts.global_completed sourceEq typesEq completedEq globalAt
  have assigned := facts.assigned_nonpending modelTypes path ready observed
  have checked := facts.global_check sourceEq functionEq typesEq completedEq globalAt ready observed assigned
  have actualCheck : check (lower module) facts.func facts.types facts.state = true := by
    simpa only [sourceEq] using checked
  rw [actualCheck] at outcome
  refine ⟨facts.state, ?_⟩
  simpa only [calleesEq, functionEq, typesEq, ↓reduceIte] using outcome

#print axioms accepted_global_closeFunction
#print axioms SourceReadyFunction.global_check

end Goose.Lower.Validation.ReplacementContentFlowSource
