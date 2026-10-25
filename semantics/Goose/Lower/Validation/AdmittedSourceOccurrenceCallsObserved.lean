import Goose.Lower.Validation.AdmittedSourceCallsObserved
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLedger

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR ReplacementContentFlowSource

theorem AdmittedSourceCalls.content_receiver_physical
    {module : Core.Module} {callerId calleeId : ContextId}
    {caller callee : Context} {callerImpl calleeImpl : Impl}
    {env : PEnv} {upper : Prov} {before after : RState}
    {syntaxArgs : List Arg} {argumentRoots : List (List RootRef)}
    {sourceRoots : List RootRef} {arguments : List ValueId} {address : ValueId} {index : Nat}
    (accepted : Core.validate module = .ok ())
    (callerFound : module.contexts[callerId]? = some caller)
    (callerImplFound : module.impls[caller.impl]? = some callerImpl)
    (calleeFound : module.contexts[calleeId]? = some callee)
    (calleeImplFound : module.impls[callee.impl]? = some calleeImpl)
    (access : env.access = ⟨module, callerImpl, caller⟩)
    (argumentsReplay : rpArgs env syntaxArgs before = .ok (argumentRoots, after))
    (contentChecked : checkContents env calleeId syntaxArgs argumentRoots = .ok ())
    (sourceFound : argumentRoots[index]? = some sourceRoots)
    (argument : arguments[index]? = some address)
    (observed : ((lowerContextAt module callee calleeImpl).roots.contents.find?
      (·.1 == index)).isSome = true)
    (physicalArguments : CallArgumentsPhysical env upper syntaxArgs arguments) :
    ∃ mutability place declared,
      syntaxArgs[index]? = some (.byRef mutability place) ∧
      (callee.contentRoots.find? (·.1 == index)).map (·.2) = some declared ∧
      checkContent env callee syntaxArgs argumentRoots index = .ok () ∧
      ReadAddressPhysical env place (rootsAt upper.vals address) := by
  have moduleEq : env.mod = module := congrArg AccessEnv.mod access
  have indexBound : index < syntaxArgs.length := by
    rw [← AdmittedSourceCalls.rpArgs_length argumentsReplay]
    exact (List.getElem?_eq_some_iff.mp sourceFound).1
  obtain ⟨declared, nativeRow⟩ : ∃ declared,
      (index, declared) ∈ (lowerContextAt module callee calleeImpl).roots.contents.toList := by
    cases found : (lowerContextAt module callee calleeImpl).roots.contents.find? (·.1 == index) with
    | none => simp [found] at observed
    | some entry =>
      have listFound := found
      rw [← Array.find?_toList] at listFound
      obtain ⟨key, declared⟩ := entry
      have same : key = index := by simpa using List.find?_some listFound
      subst key
      exact ⟨declared, List.mem_of_find?_eq_some listFound⟩
  obtain ⟨formal, formalFound, contentRow⟩ :=
    AdmittedSourceCalls.lowerContextAt_content_row_source nativeRow
  have aligned : formal.var = index :=
    ((Core.Sound.validate_modOk module accepted).impl callee.impl calleeImpl calleeImplFound |>.params
      index formal formalFound).1
  have row : (callee.contentRoots.find? (·.1 == index)).map (·.2) = some declared := by
    simpa only [aligned] using contentRow
  have checked := Core.Sound.checkContents_ok env calleeId syntaxArgs argumentRoots callee
    contentChecked (by simpa only [moduleEq] using calleeFound) index indexBound
  obtain ⟨mapped, mappedChecked, localReceiver | parameterReceiver⟩ :=
    AdmittedSourceCalls.checkContent_receiver_bounds checked row
  · obtain ⟨mutability, slot, ceiling, syntaxArgument, annotation, rest⟩ := localReceiver
    exact ⟨mutability, .var slot, declared, syntaxArgument, row, checked,
      physicalArguments index address (.byRef mutability (.var slot))
        argument syntaxArgument mutability (.var slot) rfl ⟨slot, .inl rfl⟩⟩
  · obtain ⟨mutability, variableId, ceiling, syntaxArgument, contents, rest⟩ := parameterReceiver
    have reference := AdmittedSourceCalls.accepted_content_reference accepted callerFound
      callerImplFound access contents
    exact ⟨mutability, .deref (.read (.var variableId)), declared, syntaxArgument, row, checked,
      physicalArguments index address (.byRef mutability (.deref (.read (.var variableId))))
        argument syntaxArgument mutability (.deref (.read (.var variableId))) rfl
        ⟨variableId, .inr ⟨rfl, reference, by simp [contents]⟩⟩⟩

theorem ReplacementContentFlowSource.CallOccurrence.parameter_observed
    {module : Core.Module} {callerId calleeId : ContextId}
    {caller callee : Context} {callerImpl calleeImpl : Impl}
    {env : PEnv} {root : DemandNode} {provenance upper : Prov}
    {value address : ValueId} {arguments : List ValueId} {origin : Option OriginId}
    {index parameter : Nat}
    (accepted : Core.validate module = .ok ())
    (callerFound : module.contexts[callerId]? = some caller)
    (callerImplFound : module.impls[caller.impl]? = some callerImpl)
    (calleeFound : module.contexts[calleeId]? = some callee)
    (calleeImplFound : module.impls[callee.impl]? = some calleeImpl)
    (access : env.access = ⟨module, callerImpl, caller⟩)
    (occurrence : CallOccurrence env root (lowerContextAt module caller callerImpl) upper
      value calleeId arguments origin)
    (argument : arguments[index]? = some address)
    (observed : ((lowerContextAt module callee calleeImpl).roots.contents.find?
      (·.1 == index)).isSome = true)
    (below : rootsAt provenance.vals address ⊆ rootsAt upper.vals address)
    (member : RootRef.param parameter ∈ rootsAt provenance.vals address) :
    ((lowerContextAt module caller callerImpl).roots.contents.find?
      (·.1 == parameter)).isSome = true := by
  obtain ⟨localEnv, path, syntaxArgs, sourceOrigin, before, argumentRoots, argumentsAfter,
    resultRoots, after, localAccess, originEq, node, argumentsReplay, contentChecked, callReplay,
    valueBound, valueRefined, argumentOrigins, physicalArguments, _⟩ := occurrence
  have localActual := localAccess.trans access
  obtain ⟨bound, sourceRoots, sourceFound, refined⟩ := argumentOrigins index address argument
  obtain ⟨mutability, place, declared, syntaxArgument, row, checked, physical⟩ :=
    AdmittedSourceCalls.content_receiver_physical accepted callerFound callerImplFound calleeFound
      calleeImplFound localActual argumentsReplay contentChecked sourceFound argument observed physicalArguments
  cases physical with
  | «local» variableId source exactRoots =>
    have impossible := below member
    rw [exactRoots] at impossible
    simp at impossible
  | contents variableId source reference exactRoots =>
    subst place
    exact AdmittedSourceInstructions.lowerContextAt_forwarded_parameter_observed_below
      accepted callerImplFound (congrArg AccessEnv.impl localActual)
      (congrArg AccessEnv.ctx localActual) reference checked row syntaxArgument exactRoots below member

theorem ReplacementContentFlowSource.InstructionOccurrences.call_observed
    {module : Core.Module} {callerId calleeId : ContextId}
    {caller callee : Context} {callerImpl calleeImpl : Impl}
    {env : PEnv} {root : DemandNode} {provenance upper : Prov}
    {types : Array (Option VTy)} {inst : Inst}
    {value address : ValueId} {arguments : List ValueId} {origin : Option OriginId}
    {index parameter : Nat}
    (accepted : Core.validate module = .ok ())
    (callerFound : module.contexts[callerId]? = some caller)
    (callerImplFound : module.impls[caller.impl]? = some callerImpl)
    (calleeFound : module.contexts[calleeId]? = some callee)
    (calleeImplFound : module.impls[callee.impl]? = some calleeImpl)
    (access : env.access = ⟨module, callerImpl, caller⟩)
    (occurrence : InstructionOccurrences env root (lowerContextAt module caller callerImpl)
      types upper inst)
    (call : inst = .def value (.call calleeId arguments origin))
    (argument : arguments[index]? = some address)
    (observed : ((lowerContextAt module callee calleeImpl).roots.contents.find?
      (·.1 == index)).isSome = true)
    (below : rootsAt provenance.vals address ⊆ rootsAt upper.vals address)
    (member : RootRef.param parameter ∈ rootsAt provenance.vals address) :
    ((lowerContextAt module caller callerImpl).roots.contents.find?
      (·.1 == parameter)).isSome = true :=
  (occurrence.2.2.1 value calleeId arguments origin call).parameter_observed
    accepted callerFound callerImplFound calleeFound calleeImplFound access
    argument observed below member

end Goose.Lower.Validation
