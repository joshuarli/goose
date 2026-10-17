import Goose.Lower.Validation.SourceOperandQueryBounds
import Goose.Lower.Validation.ReplacementQueryBounds

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR ReplacementContentFlowSource

theorem lowerContext_call_result_queries_within_provenance_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : ContextId} {context : Context} {impl : Impl}
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {block : GIR.Block} (member : block ∈ (lowerContextAt module context impl).blocks.toList)
    {instruction : Inst} (instructionMember : instruction ∈ block.insts)
    {value callee : ValueId} {arguments : List ValueId} {origin : Option OriginId}
    (called : instruction = .def value (.call callee arguments origin)) :
    let func := lowerContextAt module context impl
    let types := func.valueTypes (lower module)
    let rootsAtValue := rootsAt (func.provenance
      (resultRoots (lower module) (lower module).implTypes) types (lower module).rootCount).vals
    ReplacementRootsWithin ((replacementQueries (lower module) func types).value value)
      ((rootsAtValue value).flatMap func.expandParameterRoot) ∧
    ReplacementRootsWithin ((replacementQueries (lower module) func types).ownerDependencies value)
      ((rootsAtValue value).flatMap func.expandParameterRoot) := by
  subst instruction
  dsimp only
  have valueKnown := accepted_context_factory_call_value_known accepted contextAt implAt member instructionMember
  have valueBound := lowerContext_canonical_definition_bounds module context impl block member
    value (.call callee arguments origin) instructionMember
  have valueQuery : ReplacementRootsWithin
      ((replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))).value value)
      ((rootsAt ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount).vals value).flatMap
          (lowerContextAt module context impl).expandParameterRoot) := by
    obtain ⟨roots, known⟩ := valueKnown
    rw [replacementQueries_value _ _ _ _ valueBound] at known
    exact ⟨roots, (replacementQueries_value _ _ _ _ valueBound).trans known,
      lowerContext_factory_value_within_provenance_of_accepted accepted contextAt implAt known⟩
  exact ⟨valueQuery, ReplacementRootsWithin.ownerDependencies valueBound valueQuery⟩

theorem lowerGlobal_call_result_queries_within_provenance_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : GlobalId} {global : Core.Global}
    (globalAt : module.globals[index]? = some global)
    {block : GIR.Block} (member : block ∈ (lowerGlobal module global).init.blocks.toList)
    {instruction : Inst} (instructionMember : instruction ∈ block.insts)
    {value callee : ValueId} {arguments : List ValueId} {origin : Option OriginId}
    (called : instruction = .def value (.call callee arguments origin)) :
    let func := (lowerGlobal module global).init
    let types := func.valueTypes (lower module)
    let rootsAtValue := rootsAt (func.provenance
      (resultRoots (lower module) (lower module).implTypes) types (lower module).rootCount).vals
    ReplacementRootsWithin ((replacementQueries (lower module) func types).value value)
      ((rootsAtValue value).flatMap func.expandParameterRoot) ∧
    ReplacementRootsWithin ((replacementQueries (lower module) func types).ownerDependencies value)
      ((rootsAtValue value).flatMap func.expandParameterRoot) := by
  subst instruction
  dsimp only
  have valueKnown := accepted_global_factory_call_value_known accepted globalAt member instructionMember
  have valueBound := lowerGlobal_canonical_definition_bounds module global block member
    value (.call callee arguments origin) instructionMember
  have valueQuery : ReplacementRootsWithin
      ((replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))).value value)
      ((rootsAt ((lowerGlobal module global).init.provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount).vals value).flatMap
          (lowerGlobal module global).init.expandParameterRoot) := by
    obtain ⟨roots, known⟩ := valueKnown
    rw [replacementQueries_value _ _ _ _ valueBound] at known
    exact ⟨roots, (replacementQueries_value _ _ _ _ valueBound).trans known,
      lowerGlobal_factory_value_within_provenance_of_accepted accepted globalAt known⟩
  exact ⟨valueQuery, ReplacementRootsWithin.ownerDependencies valueBound valueQuery⟩

#print axioms lowerContext_call_result_queries_within_provenance_of_accepted
#print axioms lowerGlobal_call_result_queries_within_provenance_of_accepted

end Goose.Lower.Validation
