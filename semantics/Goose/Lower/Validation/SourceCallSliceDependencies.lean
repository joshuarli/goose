import Goose.Lower.Validation.SourceReadyCallSliceDependencies
import Goose.Lower.Validation.ReplacementQueryBounds

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR ReplacementContentFlowSource

theorem lowerContext_call_slice_dependencies_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : ContextId} {context : Context} {impl : Impl}
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {block : GIR.Block} (member : block ∈ (lowerContextAt module context impl).blocks.toList)
    {value calleeId : ValueId} {arguments : List ValueId} {origin : Option OriginId}
    (called : Inst.def value (.call calleeId arguments origin) ∈ block.insts)
    {mutability : Mutability} {element : Ty}
    (typed : ((lowerContextAt module context impl).valueTypes (lower module))[value]? =
      some (some (.data (.slice mutability element)))) :
    ∃ dependencies roots,
      ((replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))).ownerDependencies value = some dependencies) ∧
      ((replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))).callRoots calleeId arguments = some roots) ∧
      dependencies ⊆ roots := by
  obtain ⟨facts, sourceEq, functionEq, typesEq, _, model, _, observed⟩ :=
    accepted_context_factory_ready_inputs accepted contextAt implAt
  have actualModel : ((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types).model =
      some facts.state := by simpa only [sourceEq] using model
  have unique : (facts.func.blocks.toList.flatMap GIR.Block.defs).Nodup := by
    rw [functionEq]
    exact (lowerImpl_dense_definitions module impl).nodup_iff.mpr List.nodup_range
  have actualTyped : facts.types[value]? = some (some (.data (.slice mutability element))) := by
    simpa only [typesEq] using typed
  obtain ⟨dependencies, roots, dependencyAt, callAt, included⟩ :=
    facts.call_slice_dependencies actualModel observed unique (functionEq ▸ member) called actualTyped
  have bounded := lowerContext_canonical_definition_bounds module context impl block member
    value (.call calleeId arguments origin) called
  refine ⟨dependencies, roots, ?_, ?_, included⟩
  · rw [replacementQueries_ownerDependencies _ _ _ _ bounded]
    simpa only [sourceEq, functionEq, typesEq] using dependencyAt
  · change ReplacementFunctionFlow.call ((replacementContentFlow (lower module)).forFunction
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)))
      calleeId arguments = some roots
    simpa only [sourceEq, functionEq, typesEq] using callAt

theorem lowerGlobal_call_slice_dependencies_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : GlobalId} {global : Core.Global}
    (globalAt : module.globals[index]? = some global)
    {block : GIR.Block} (member : block ∈ (lowerGlobal module global).init.blocks.toList)
    {value calleeId : ValueId} {arguments : List ValueId} {origin : Option OriginId}
    (called : Inst.def value (.call calleeId arguments origin) ∈ block.insts)
    {mutability : Mutability} {element : Ty}
    (typed : ((lowerGlobal module global).init.valueTypes (lower module))[value]? =
      some (some (.data (.slice mutability element)))) :
    ∃ dependencies roots,
      ((replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))).ownerDependencies value = some dependencies) ∧
      ((replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))).callRoots calleeId arguments = some roots) ∧
      dependencies ⊆ roots := by
  obtain ⟨facts, sourceEq, functionEq, typesEq, _, model, _, observed⟩ :=
    accepted_global_factory_ready_inputs accepted globalAt
  have actualModel : ((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types).model =
      some facts.state := by simpa only [sourceEq] using model
  have unique : (facts.func.blocks.toList.flatMap GIR.Block.defs).Nodup := by
    rw [functionEq]
    exact (lowerGlobal_dense_definitions module global).nodup_iff.mpr List.nodup_range
  have actualTyped : facts.types[value]? = some (some (.data (.slice mutability element))) := by
    simpa only [typesEq] using typed
  obtain ⟨dependencies, roots, dependencyAt, callAt, included⟩ :=
    facts.call_slice_dependencies actualModel observed unique (functionEq ▸ member) called actualTyped
  have bounded := lowerGlobal_canonical_definition_bounds module global block member
    value (.call calleeId arguments origin) called
  refine ⟨dependencies, roots, ?_, ?_, included⟩
  · rw [replacementQueries_ownerDependencies _ _ _ _ bounded]
    simpa only [sourceEq, functionEq, typesEq] using dependencyAt
  · change ReplacementFunctionFlow.call ((replacementContentFlow (lower module)).forFunction
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)))
      calleeId arguments = some roots
    simpa only [sourceEq, functionEq, typesEq] using callAt

#print axioms lowerGlobal_call_slice_dependencies_of_accepted
#print axioms lowerContext_call_slice_dependencies_of_accepted

end Goose.Lower.Validation
