import Goose.Lower.Validation.SourceReplacementCallContentsApartOwners
import Goose.Lower.Validation.SourceReadyFactory

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem canonical_call_content_receiver_bound
    {module : Core.Module} {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {provenance upper : Prov} {state : State} {results : Array (List RootRef)}
    (accepted : Core.validate module = .ok ()) (envModule : env.mod = module)
    (native : FunctionCanonicalFacts (lower module) func types provenance results)
    (canonical : state.CanonicalWithin func types provenance)
    (below : ∀ value, rootsAt provenance.vals value ⊆ rootsAt upper.vals value)
    {block : GIR.Block} {value calleeId index argument : Nat}
    {arguments : List ValueId} {origin : Option OriginId}
    {callee : Context} {implementation : Impl} {declared : List RootRef}
    (member : block ∈ func.blocks.toList)
    (called : Inst.def value (.call calleeId arguments origin) ∈ block.insts)
    (calleeAt : module.contexts[calleeId]? = some callee)
    (implementationAt : module.impls[callee.impl]? = some implementation)
    (occurrence : CallOccurrence env root func upper
      value calleeId arguments origin)
    (annotation : (lowerContextAt module callee implementation).roots.contents.find?
      (·.1 == index) = some (index, declared))
    (argumentAt : arguments[index]? = some argument)
    (available : CallObservationReady (lowerContextAt module callee implementation)
      func state arguments) :
    ∃ (localEnv : PEnv) (path : List Nat) (syntaxArgs : List Arg) (sourceOrigin : OriginId)
        (ceiling actual : List RootRef),
      localEnv.access = env.access ∧
      DemandNodeAt root path (.expression (.call calleeId syntaxArgs sourceOrigin)) ∧
      CallArgumentsTrace localEnv syntaxArgs arguments func calleeId sourceOrigin ∧
      CallArgumentsPhysical localEnv upper syntaxArgs arguments ∧
      normalize func (content func state (flowAt state.values argument)) = some actual ∧
      actual ⊆ ceiling.flatMap func.expandParameterRoot ∧
      ((∃ mutability slot, syntaxArgs[index]? = some (.byRef mutability (.var slot)) ∧
        localEnv.ann slot = some ceiling) ∨
        (∃ mutability parameter, syntaxArgs[index]? =
          some (.byRef mutability (.deref (.read (.var parameter)))) ∧ localEnv.cont parameter = some ceiling)) := by
  obtain ⟨localEnv, path, syntaxArgs, sourceOrigin, before, sourceRoots, argumentsAfter,
    returned, after, access, _, source, replayed, contentsChecked, callReplayed, _, _, argumentOrigins, physical, trace⟩ := occurrence
  have moduleEq : localEnv.mod = module := (congrArg AccessEnv.mod access).trans envModule
  obtain ⟨typedContext, typedImpl, checkedContext, checkedImpl, checkedArguments, rest⟩ :=
    rpCall_ok localEnv calleeId sourceRoots argumentsAfter returned after callReplayed
  have checkedContextRow : module.contexts[calleeId]? = some typedContext := by
    simpa only [moduleEq] using checkedContext
  have contextEq : typedContext = callee := Option.some.inj (checkedContextRow.symm.trans calleeAt)
  subst typedContext
  have checkedImplRow : module.impls[callee.impl]? = some typedImpl := by
    simpa only [moduleEq] using checkedImpl
  have implEq : typedImpl = implementation := Option.some.inj (checkedImplRow.symm.trans implementationAt)
  subst typedImpl
  have savedTrace := trace
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, typingEnv, start, finish, type,
    typingModule, typingVariables, typedCall⟩ := trace
  obtain ⟨typedContext, typedImpl, argsStart, argsFinish, _, typedContextAt, typedImplAt, arity, _, _⟩ :=
    tyExpr_call_tables typedCall
  rw [typingModule, checkedContext] at typedContextAt
  cases Option.some.inj typedContextAt
  rw [typingModule, checkedImpl] at typedImplAt
  cases Option.some.inj typedImplAt
  have sourceArity : syntaxArgs.length = implementation.params.size := by
    simpa only [Array.length_toList] using arity.symm
  have nativeMember : (index, declared) ∈
      (lowerContextAt module callee implementation).roots.contents.toList := by
    rw [← Array.find?_toList] at annotation
    exact List.mem_of_find?_eq_some annotation
  obtain ⟨mapped, mapping, receivers⟩ := AdmittedSourceCalls.checkContents_native_row_receiver_bounds
    accepted calleeAt implementationAt moduleEq contentsChecked sourceArity nativeMember
  have nativeAt := lower_func_at calleeAt implementationAt
  have calleeRoots := (lowerContext_canonical_facts_of_accepted accepted calleeAt implementationAt).roots
  obtain ⟨found, actual, foundAt, known, within⟩ := call_content_source_bound
    native canonical member called nativeAt calleeRoots annotation mapping (by
      intro parameter value roots included argumentRow rootsRow
      obtain ⟨_, selected, selectedAt, refined⟩ := argumentOrigins parameter value argumentRow
      have same : selected = roots := Option.some.inj (selectedAt.symm.trans rootsRow)
      subst selected
      exact refined.actual_mono (below value)) available
  have same : found = argument := Option.some.inj (foundAt.symm.trans argumentAt)
  subst found
  rcases receivers with ⟨mutability, slot, ceiling, syntaxArgument, annotationAt, upper, lower⟩ |
    ⟨mutability, parameter, ceiling, syntaxArgument, contentsAt, upper, lower⟩
  · refine ⟨localEnv, path, syntaxArgs, sourceOrigin, ceiling, actual, access, source, savedTrace, physical, known, ?_,
      .inl ⟨mutability, slot, syntaxArgument, annotationAt⟩⟩
    intro root rootAt
    obtain ⟨source, sourceAt, expandedAt⟩ := List.mem_flatMap.mp (within rootAt)
    exact List.mem_flatMap.mpr ⟨source, upper sourceAt, expandedAt⟩
  · refine ⟨localEnv, path, syntaxArgs, sourceOrigin, ceiling, actual, access, source, savedTrace, physical, known, ?_,
      .inr ⟨mutability, parameter, syntaxArgument, contentsAt⟩⟩
    intro root rootAt
    obtain ⟨source, sourceAt, expandedAt⟩ := List.mem_flatMap.mp (within rootAt)
    exact List.mem_flatMap.mpr ⟨source, upper sourceAt, expandedAt⟩

theorem accepted_context_final_call_observation {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {implementation : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implementationAt : module.impls[context.impl]? = some implementation)
    {final : State}
    (modelAt : ((replacementContentFlow (lower module)).forFunction
      (lowerContextAt module context implementation)
      ((lowerContextAt module context implementation).valueTypes (lower module))).model = some final)
    {block : GIR.Block} (member : block ∈ (lowerContextAt module context implementation).blocks.toList)
    {value function : Nat} {arguments : List ValueId} {origin : Option OriginId}
    (called : Inst.def value (.call function arguments origin) ∈ block.insts)
    {callee : Func} (calleeAt : (lower module).funcs[function]? = some callee) :
    CallObservationReady callee (lowerContextAt module context implementation) final arguments := by
  obtain ⟨facts, sourceEq, functionEq, typesEq, completedEq, model, _, observed⟩ :=
    accepted_context_factory_ready_inputs accepted contextAt implementationAt
  have actualModel : ((replacementContentFlow (lower module)).forFunction
      (lowerContextAt module context implementation)
      ((lowerContextAt module context implementation).valueTypes (lower module))).model = some facts.state := by
    simpa only [functionEq, typesEq] using model
  have stateEq : facts.state = final := Option.some.inj (actualModel.symm.trans modelAt)
  have actualObserved : ∀ instruction ∈ (cfg_implState module implementation).insts,
      ReadyCallObservations (lower module) (lowerContextAt module context implementation) final instruction := by
    simpa only [sourceEq, functionEq, completedEq, stateEq] using observed
  have emitted := finishBlocks_instruction_member
    (by simpa only [cfg_context_blocks] using member) called
  exact actualObserved _ emitted value function arguments origin rfl callee calleeAt

theorem site_call_content_receiver_bound_of_accepted {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {implementation : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implementationAt : module.impls[context.impl]? = some implementation)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, implementation, context, []⟩ (.block implementation.body) []
      (lowerEnv module implementation.vars implementation.results.toList) (cfg_implState module implementation)
      (lowerContextAt module context implementation)
      ((lowerContextAt module context implementation).valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (below : ProvenanceBelow
      ((lowerContextAt module context implementation).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context implementation).valueTypes (lower module)) (lower module).rootCount) upper)
    {final : State}
    (finalAt : ((replacementContentFlow (lower module)).forFunction
      (lowerContextAt module context implementation)
      ((lowerContextAt module context implementation).valueTypes (lower module))).model = some final)
    {block : GIR.Block} (member : block ∈ (lowerContextAt module context implementation).blocks.toList)
    {value function index argument : Nat} {arguments : List ValueId} {callOrigin : Option OriginId}
    (called : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    {callee : Context} {calleeImpl : Impl} {declared : List RootRef}
    (calleeAt : module.contexts[function]? = some callee)
    (calleeImplAt : module.impls[callee.impl]? = some calleeImpl)
    (occurrence : CallOccurrence site.localEnv (.expression site.source.site.source.rhs)
      (lowerContextAt module context implementation) upper value function arguments callOrigin)
    (annotation : (lowerContextAt module callee calleeImpl).roots.contents.find? (·.1 == index) = some (index, declared))
    (argumentAt : arguments[index]? = some argument) :
    ∃ (localEnv : PEnv) (path : List Nat) (syntaxArgs : List Arg) (sourceOrigin : OriginId)
        (ceiling actual : List RootRef),
      localEnv.access = site.localEnv.access ∧
      DemandNodeAt (.expression site.source.site.source.rhs) path (.expression (.call function syntaxArgs sourceOrigin)) ∧
      CallArgumentsTrace localEnv syntaxArgs arguments (lowerContextAt module context implementation) function sourceOrigin ∧
      CallArgumentsPhysical localEnv upper syntaxArgs arguments ∧
      normalize (lowerContextAt module context implementation)
        (content (lowerContextAt module context implementation) final (flowAt final.values argument)) = some actual ∧
      actual ⊆ ceiling.flatMap (lowerContextAt module context implementation).expandParameterRoot ∧
      ((∃ mutability slot, syntaxArgs[index]? = some (.byRef mutability (.var slot)) ∧
        localEnv.ann slot = some ceiling) ∨
        (∃ mutability parameter, syntaxArgs[index]? =
          some (.byRef mutability (.deref (.read (.var parameter)))) ∧ localEnv.cont parameter = some ceiling)) := by
  have native := lowerContext_canonical_facts_of_accepted accepted contextAt implementationAt
  obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  have canonical := ReplacementContentFlow.forFunction_canonicalWithin native
    (lower_canonical_facts_of_accepted accepted) annotations entries addresses finalAt
  have nativeCalleeAt := lower_func_at calleeAt calleeImplAt
  have available := accepted_context_final_call_observation accepted contextAt implementationAt
    finalAt member called nativeCalleeAt
  exact canonical_call_content_receiver_bound accepted (congrArg AccessEnv.mod site.access)
    native canonical below.vals member called calleeAt calleeImplAt occurrence annotation argumentAt available

#print axioms canonical_call_content_receiver_bound
#print axioms accepted_context_final_call_observation
#print axioms site_call_content_receiver_bound_of_accepted

end Goose.Lower.Validation
