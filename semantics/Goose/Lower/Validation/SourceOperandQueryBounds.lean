import Goose.Lower.Validation.SourceReadyQueryKnown
import Goose.Lower.Validation.SourceReplacementQueryBounds
import Goose.Lower.Validation.ReplacementQueryBounds
import Goose.Lower.Validation.OperandFunctions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR ReplacementContentFlowSource

theorem lowerContext_operand_queries_within_provenance_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : ContextId} {context : Context} {impl : Impl}
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {block : GIR.Block} (member : block ∈ (lowerContextAt module context impl).blocks.toList)
    {instruction : Inst} (instructionMember : instruction ∈ block.insts)
    {value : ValueId} (used : value ∈ instruction.uses) :
    let func := lowerContextAt module context impl
    let types := func.valueTypes (lower module)
    let upper := (rootsAt (func.provenance
      (resultRoots (lower module) (lower module).implTypes) types (lower module).rootCount).vals value).flatMap
        func.expandParameterRoot
    ReplacementRootsWithin ((replacementQueries (lower module) func types).value value) upper ∧
      ReplacementRootsWithin ((replacementQueries (lower module) func types).ownerDependencies value) upper := by
  dsimp only
  have bounded := (lowerContextAt_operand_bounds module context impl).1 block member instruction instructionMember value used
  obtain ⟨roots, known⟩ :=
    accepted_context_factory_operand_value accepted contextAt implAt member instructionMember used
  have within : ReplacementRootsWithin
      ((replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))).value value)
      ((rootsAt ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount).vals value).flatMap
          (lowerContextAt module context impl).expandParameterRoot) :=
    ⟨roots, (replacementQueries_value _ _ _ _ bounded).trans known,
      lowerContext_factory_value_within_provenance_of_accepted accepted contextAt implAt known⟩
  exact ⟨within, ReplacementRootsWithin.ownerDependencies bounded within⟩

theorem lowerGlobal_operand_queries_within_provenance_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : GlobalId} {global : Core.Global}
    (globalAt : module.globals[index]? = some global)
    {block : GIR.Block} (member : block ∈ (lowerGlobal module global).init.blocks.toList)
    {instruction : Inst} (instructionMember : instruction ∈ block.insts)
    {value : ValueId} (used : value ∈ instruction.uses) :
    let func := (lowerGlobal module global).init
    let types := func.valueTypes (lower module)
    let upper := (rootsAt (func.provenance
      (resultRoots (lower module) (lower module).implTypes) types (lower module).rootCount).vals value).flatMap
        func.expandParameterRoot
    ReplacementRootsWithin ((replacementQueries (lower module) func types).value value) upper ∧
      ReplacementRootsWithin ((replacementQueries (lower module) func types).ownerDependencies value) upper := by
  dsimp only
  have bounded := (lowerGlobal_operand_bounds module global).1 block member instruction instructionMember value used
  obtain ⟨roots, known⟩ :=
    accepted_global_factory_operand_value accepted globalAt member instructionMember used
  have within : ReplacementRootsWithin
      ((replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))).value value)
      ((rootsAt ((lowerGlobal module global).init.provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount).vals value).flatMap
          (lowerGlobal module global).init.expandParameterRoot) :=
    ⟨roots, (replacementQueries_value _ _ _ _ bounded).trans known,
      lowerGlobal_factory_value_within_provenance_of_accepted accepted globalAt known⟩
  exact ⟨within, ReplacementRootsWithin.ownerDependencies bounded within⟩

#print axioms lowerContext_operand_queries_within_provenance_of_accepted
#print axioms lowerGlobal_operand_queries_within_provenance_of_accepted

end Goose.Lower.Validation
