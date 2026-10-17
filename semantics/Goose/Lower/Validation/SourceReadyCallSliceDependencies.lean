import Goose.Lower.Validation.SourceReadySliceOrigins
import Goose.GIR.ReplacementContentFlowProofsCallResultOrigins

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFunction.call_slice_dependencies (facts : SourceReadyFunction)
    (model : ((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types).model =
      some facts.state)
    (observed : ∀ instruction ∈ facts.completed.insts,
      ReadyCallObservations (lower facts.source.mod) facts.func facts.state instruction)
    (unique : (facts.func.blocks.toList.flatMap GIR.Block.defs).Nodup)
    {block : GIR.Block} (blockMember : block ∈ facts.func.blocks.toList)
    {value calleeId : ValueId} {arguments : List ValueId} {origin : Option OriginId}
    (called : Inst.def value (.call calleeId arguments origin) ∈ block.insts)
    {mutability : Mutability} {element : Ty}
    (typed : facts.types[value]? = some (some (.data (.slice mutability element)))) :
    ∃ dependencies roots,
      ((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types).ownerDependencies value =
        some dependencies ∧
      ((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types).call calleeId arguments =
        some roots ∧ dependencies ⊆ roots := by
  obtain ⟨typesEq, states, statesAt, fixed, checked⟩ :=
    ReplacementContentFlow.forFunction_model_checked model
  have sourceEq := replacementContentFlow_source (lower facts.source.mod)
  have canonicalTypes : facts.types = facts.func.valueTypes (lower facts.source.mod) := by
    simpa only [sourceEq] using typesEq
  have closure := (replacementContentFlow_model_checked statesAt).2.1
  obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted facts.accepted
  have moduleFacts := lower_canonical_facts_of_accepted facts.accepted
  have canonical := close_canonicalWithin moduleFacts annotations entries addresses closure
  have finite := canonical.2
  have sliceOrigins := accepted_module_slice_origins facts.accepted closure
  have touchRows := close_touchRows moduleFacts annotations entries addresses closure
  have touches := (close_reachable closure).observedTouches moduleFacts
    (moduleStart_finite _ _ annotations entries) addresses
  obtain ⟨site⟩ := facts.native.calls block blockMember value calleeId arguments origin called
  obtain ⟨effects, effectsAt, effectsCanonical⟩ := canonical.1.2 calleeId site.callee site.calleeAt
  have calleeFacts := moduleFacts.functions calleeId site.callee site.calleeAt
  have effectsOrigins := sliceOrigins calleeId site.callee effects site.calleeAt effectsAt
  have effectsSupported := finite.1 calleeId site.callee effects site.calleeAt effectsAt
  have effectsRows := touchRows calleeId site.callee effects site.calleeAt effectsAt
  have effectsTouched := touches calleeId site.callee effects site.calleeAt effectsAt
  have emitted := finishBlocks_instruction_member (facts.frame.blocks ▸ blockMember) called
  have available := observed _ emitted value calleeId arguments origin rfl site.callee site.calleeAt
  have calleeResult : site.callee.results = [.slice mutability element] := by
    rcases facts.native.callResults block blockMember value calleeId arguments origin called site.callee site.calleeAt with
      ⟨empty, unit⟩ | ⟨type, results, typeAt⟩
    · rw [unit] at typed
      cases typed
    · have same : type = .slice mutability element := by
        simpa only [Option.some.injEq, VTy.data.injEq] using typeAt.symm.trans typed
      simpa only [same] using results
  obtain ⟨roots, queryKnown⟩ := facts.call_query_known model observed blockMember called
  have rawQuery : callQuery (lower facts.source.mod) facts.func facts.types states facts.state
      calleeId arguments = some roots := by
    rw [ReplacementFunctionFlow.call_model] at queryKnown
    change (((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types).model.bind
      fun state => (replacementContentFlow (lower facts.source.mod)).model.bind fun callees =>
        callQuery (lower facts.source.mod) facts.func
          (facts.func.valueTypes (lower facts.source.mod)) callees state calleeId arguments) = some roots at queryKnown
    simpa only [model, statesAt, Option.bind_some, ← canonicalTypes] using queryKnown
  have localBuilt := model
  rw [ReplacementContentFlow.forFunction_model] at localBuilt
  simp only [sourceEq, canonicalTypes, beq_self_eq_true, ↓reduceIte, statesAt, Option.bind_some] at localBuilt
  have reachable := closeFunctionFrom_reachable localBuilt
  have bounded := facts.native.definitions block blockMember value (.call calleeId arguments origin) called
  have atomBound : (flowAt facts.state.values value).AtomsWithin
      (OwnerDependencyAtom (lower facts.source.mod) facts.func roots) := by
    apply reachable.call_value (.refl facts.state) unique bounded blockMember called site.calleeAt effectsAt
    intro before growth
    exact call_slice_return_observed facts.native site effectsAt calleeFacts.roots calleeResult
      effectsCanonical effectsOrigins effectsSupported effectsRows effectsTouched growth available rawQuery blockMember called
  obtain ⟨returned, valueKnown⟩ := facts.call_value_known model observed blockMember called
  obtain ⟨dependencies, dependencyKnown, _⟩ := ReplacementFunctionFlow.ownerDependencies_of_value valueKnown
  have rawDependencies := dependencyKnown
  rw [ReplacementFunctionFlow.ownerDependencies_model] at rawDependencies
  simp only [model, Option.bind_some] at rawDependencies
  exact ⟨dependencies, roots, dependencyKnown, queryKnown,
    ownerDependencies_within_of_atomsWithin atomBound rawDependencies⟩

#print axioms SourceReadyFunction.call_slice_dependencies

end Goose.Lower.Validation.ReplacementContentFlowSource
