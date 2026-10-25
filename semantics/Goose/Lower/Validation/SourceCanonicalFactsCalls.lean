import Goose.Lower.Validation.SourceCanonicalFactsCallTyping
import Goose.Lower.Validation.SourceCanonicalFactsInstructions
import Goose.Lower.Validation.SourceOccurrenceInstructions
import Goose.Lower.Validation.AdmittedSourceOccurrenceCalls
import Goose.Lower.Validation.AdmittedSourceOccurrenceCallsObserved
import Goose.Lower.Validation.ReplacementContentFlowSourceShape
import Goose.Lower.Validation.OperandFunctions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem lowerContext_canonical_calls_of_accepted {module : Core.Module}
    {context : Context} {impl : Impl} {index : ContextId}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl) :
    ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ value callee arguments origin,
      Inst.def value (.call callee arguments origin) ∈ block.insts →
      Nonempty (CallSiteFacts (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))
        ((lowerContextAt module context impl).provenance
          (resultRoots (lower module) (lower module).implTypes)
          ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount)
        callee arguments) := by
  obtain ⟨upper, below, instructions⟩ := accepted_context_instruction_occurrences accepted contextAt implAt
  intro block blockMember value function arguments origin callMember
  have occurrence := (instructions block blockMember _ callMember).2.2.1 value function arguments origin rfl
  have typing := lowerContext_instructionCanonicalFacts_of_accepted accepted contextAt implAt
    block blockMember _ callMember
  cases typing with
  | definition _ _ type typed canonical =>
    have bounded : ∀ argument ∈ arguments, argument < (lowerContextAt module context impl).numValues := by
      intro argument member
      exact (lowerContextAt_operand_bounds module context impl).1 block blockMember _ callMember argument
        (by simpa [Inst.uses, Op.uses] using member)
    obtain ⟨callee, calleeAt, arity, argumentBounds, references⟩ := canonical_call_type_facts typed bounded
    obtain ⟨calleeContext, calleeImpl, calleeContextAt, calleeImplAt, rfl⟩ :=
      accepted_function_context accepted calleeAt
    have sourceArity : arguments.length = calleeImpl.params.size := by
      simpa [lowerContextAt, lowerImpl, lowerImplFromState] using arity.symm
    refine ⟨{
      callee := lowerContextAt module calleeContext calleeImpl
      calleeAt := calleeAt
      contracts := occurrence.parameter_contracts accepted calleeContextAt calleeImplAt rfl sourceArity below.vals
      arguments := argumentBounds
      references := references
      observed := ?_ }⟩
    intro parameter argument argumentAt _ observed receiver member _
    exact occurrence.parameter_observed accepted contextAt implAt calleeContextAt calleeImplAt rfl
      argumentAt observed (below.vals argument) member


theorem lowerGlobal_canonical_calls_of_accepted {module : Core.Module}
    {global : Core.Global} {index : GlobalId}
    (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[index]? = some global) :
    ∀ block ∈ (lowerGlobal module global).init.blocks.toList, ∀ value callee arguments origin,
      Inst.def value (.call callee arguments origin) ∈ block.insts →
      Nonempty (CallSiteFacts (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))
        ((lowerGlobal module global).init.provenance
          (resultRoots (lower module) (lower module).implTypes)
          ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount)
        callee arguments) := by
  obtain ⟨upper, below, instructions⟩ := accepted_global_instruction_occurrences accepted globalAt
  intro block blockMember value function arguments origin callMember
  have occurrence := (instructions block blockMember _ callMember).2.2.1 value function arguments origin rfl
  have typing := lowerGlobal_instructionCanonicalFacts_of_accepted accepted globalAt
    block blockMember _ callMember
  cases typing with
  | definition _ _ type typed canonical =>
    have bounded : ∀ argument ∈ arguments, argument < (lowerGlobal module global).init.numValues := by
      intro argument member
      exact (lowerGlobal_operand_bounds module global).1 block blockMember _ callMember argument
        (by simpa [Inst.uses, Op.uses] using member)
    obtain ⟨callee, calleeAt, arity, argumentBounds, references⟩ := canonical_call_type_facts typed bounded
    obtain ⟨calleeContext, calleeImpl, calleeContextAt, calleeImplAt, rfl⟩ :=
      accepted_function_context accepted calleeAt
    have sourceArity : arguments.length = calleeImpl.params.size := by
      simpa [lowerContextAt, lowerImpl, lowerImplFromState] using arity.symm
    refine ⟨{
      callee := lowerContextAt module calleeContext calleeImpl
      calleeAt := calleeAt
      contracts := occurrence.parameter_contracts accepted calleeContextAt calleeImplAt rfl sourceArity below.vals
      arguments := argumentBounds
      references := references
      observed := ?_ }⟩
    intro parameter argument argumentAt reference observed receiver member receiverReference
    simp [lowerGlobal] at receiverReference

#print axioms lowerContext_canonical_calls_of_accepted
#print axioms lowerGlobal_canonical_calls_of_accepted

end Goose.Lower.Validation
