import Goose.Lower.Validation.SourceReadyCheckCalls
import Goose.Lower.Validation.SourceReplacementOwnerQueries
import Goose.Lower.Validation.ReplacementOwnerDependencyApart

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem ReplacementContentFlowSource.SourceReadyFunction.call_content_receiver_bound
    (facts : SourceReadyFunction)
    {block : GIR.Block} {value calleeId index argument : Nat}
    {arguments : List ValueId} {origin : Option OriginId}
    {callee : Context} {implementation : Impl} {declared : List RootRef}
    (member : block ∈ facts.func.blocks.toList)
    (called : Inst.def value (.call calleeId arguments origin) ∈ block.insts)
    (calleeAt : facts.source.mod.contexts[calleeId]? = some callee)
    (implementationAt : facts.source.mod.impls[callee.impl]? = some implementation)
    (occurrence : CallOccurrence facts.source facts.root facts.func facts.upper
      value calleeId arguments origin)
    (annotation : (lowerContextAt facts.source.mod callee implementation).roots.contents.find?
      (·.1 == index) = some (index, declared))
    (argumentAt : arguments[index]? = some argument)
    (available : CallObservationReady (lowerContextAt facts.source.mod callee implementation)
      facts.func facts.state arguments) :
    ∃ (localEnv : PEnv) (path : List Nat) (syntaxArgs : List Arg) (sourceOrigin : OriginId)
        (ceiling actual : List RootRef),
      localEnv.access = facts.source.access ∧
      DemandNodeAt facts.root path (.expression (.call calleeId syntaxArgs sourceOrigin)) ∧
      normalize facts.func (content facts.func facts.state (flowAt facts.state.values argument)) = some actual ∧
      actual ⊆ ceiling.flatMap facts.func.expandParameterRoot ∧
      ((∃ mutability slot, syntaxArgs[index]? = some (.byRef mutability (.var slot)) ∧
        localEnv.ann slot = some ceiling) ∨
        (∃ mutability parameter, syntaxArgs[index]? =
          some (.byRef mutability (.deref (.read (.var parameter)))) ∧ localEnv.cont parameter = some ceiling)) := by
  obtain ⟨localEnv, path, syntaxArgs, sourceOrigin, before, sourceRoots, argumentsAfter,
    returned, after, access, _, source, replayed, contentsChecked, callReplayed, _, _, argumentOrigins, _, trace⟩ := occurrence
  have moduleEq : localEnv.mod = facts.source.mod := congrArg AccessEnv.mod access
  obtain ⟨typedContext, typedImpl, checkedContext, checkedImpl, checkedArguments, rest⟩ :=
    rpCall_ok localEnv calleeId sourceRoots argumentsAfter returned after callReplayed
  have checkedContextRow : facts.source.mod.contexts[calleeId]? = some typedContext := by
    simpa only [moduleEq] using checkedContext
  have contextEq : typedContext = callee := Option.some.inj (checkedContextRow.symm.trans calleeAt)
  subst typedContext
  have checkedImplRow : facts.source.mod.impls[callee.impl]? = some typedImpl := by
    simpa only [moduleEq] using checkedImpl
  have implEq : typedImpl = implementation := Option.some.inj (checkedImplRow.symm.trans implementationAt)
  subst typedImpl
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
      (lowerContextAt facts.source.mod callee implementation).roots.contents.toList := by
    rw [← Array.find?_toList] at annotation
    exact List.mem_of_find?_eq_some annotation
  obtain ⟨mapped, mapping, receivers⟩ := AdmittedSourceCalls.checkContents_native_row_receiver_bounds
    facts.accepted calleeAt implementationAt moduleEq contentsChecked sourceArity nativeMember
  have nativeAt := lower_func_at calleeAt implementationAt
  have calleeFacts := facts.moduleFacts.functions calleeId _ nativeAt
  obtain ⟨found, actual, foundAt, known, within⟩ := call_content_source_bound
    facts.native facts.canonical member called nativeAt calleeFacts.roots annotation mapping (by
      intro parameter value roots included argumentRow rootsRow
      obtain ⟨_, selected, selectedAt, refined⟩ := argumentOrigins parameter value argumentRow
      have same : selected = roots := Option.some.inj (selectedAt.symm.trans rootsRow)
      subst selected
      exact refined.actual_mono (facts.below value)) available
  have same : found = argument := Option.some.inj (foundAt.symm.trans argumentAt)
  subst found
  rcases receivers with ⟨mutability, slot, ceiling, syntaxArgument, annotationAt, upper, lower⟩ |
    ⟨mutability, parameter, ceiling, syntaxArgument, contentsAt, upper, lower⟩
  · refine ⟨localEnv, path, syntaxArgs, sourceOrigin, ceiling, actual, access, source, known, ?_,
      .inl ⟨mutability, slot, syntaxArgument, annotationAt⟩⟩
    intro root rootAt
    obtain ⟨source, sourceAt, expandedAt⟩ := List.mem_flatMap.mp (within rootAt)
    exact List.mem_flatMap.mpr ⟨source, upper sourceAt, expandedAt⟩
  · refine ⟨localEnv, path, syntaxArgs, sourceOrigin, ceiling, actual, access, source, known, ?_,
      .inr ⟨mutability, parameter, syntaxArgument, contentsAt⟩⟩
    intro root rootAt
    obtain ⟨source, sourceAt, expandedAt⟩ := List.mem_flatMap.mp (within rootAt)
    exact List.mem_flatMap.mpr ⟨source, upper sourceAt, expandedAt⟩

theorem site_global_call_content_apart_of_accepted {module : Core.Module}
    {global : Core.Global} {upper : Prov}
    {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, Core.initImpl, Core.initContext, []⟩ (.expression global.init) []
      (lowerEnv module #[] [global.ty]) (cfg_globalState module global)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (accepted : Core.validate module = .ok ())
    {value calleeId index argument : Nat} {arguments : List ValueId} {callOrigin : Option OriginId}
    {callee : Context} {implementation : Impl}
    (calleeAt : module.contexts[calleeId]? = some callee)
    (implementationAt : module.impls[callee.impl]? = some implementation)
    (occurrence : CallOccurrence site.localEnv (.expression site.source.site.source.rhs)
      (lowerGlobal module global).init upper value calleeId arguments callOrigin)
    (argumentAt : arguments[index]? = some argument)
    (observed : ((lowerContextAt module callee implementation).roots.contents.find?
      (·.1 == index)).isSome = true)
    (current : State) :
    (content (lowerGlobal module global).init current (flowAt current.values argument)).AtomsWithin
      (OwnerDependencyApart (lower module) (lowerGlobal module global).init
        (replacementQueries (lower module) (lowerGlobal module global).init
          ((lowerGlobal module global).init.valueTypes (lower module))) owner) := by
  have moduleEq : site.localEnv.mod = module := congrArg AccessEnv.mod site.access
  have contextEq : site.localEnv.ctx = initContext := congrArg AccessEnv.ctx site.access
  exact False.elim (occurrence.no_global_content_receiver accepted moduleEq contextEq
    calleeAt implementationAt argumentAt observed)

#print axioms ReplacementContentFlowSource.SourceReadyFunction.call_content_receiver_bound
#print axioms site_global_call_content_apart_of_accepted

end Goose.Lower.Validation
