import Goose.Lower.Validation.SourceReadyInductionFacts
import Goose.Lower.Validation.AdmittedSourceOccurrenceCallsObserved

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem CallOccurrence.no_global_content_receiver
    {env : PEnv} {root : DemandNode} {func : Func} {upper : Prov}
    {module : Core.Module} {calleeId : ContextId} {callee : Context} {implementation : Impl}
    {value address : ValueId} {arguments : List ValueId} {origin : Option OriginId} {index : Nat}
    (accepted : Core.validate module = .ok ())
    (moduleEq : env.mod = module) (contextEq : env.ctx = initContext)
    (calleeRow : module.contexts[calleeId]? = some callee)
    (implementationRow : module.impls[callee.impl]? = some implementation)
    (occurrence : CallOccurrence env root func upper value calleeId arguments origin)
    (argumentRow : arguments[index]? = some address)
    (observed : ((lowerContextAt module callee implementation).roots.contents.find? (·.1 == index)).isSome = true) :
    False := by
  obtain ⟨localEnv, path, syntaxArgs, sourceOrigin, before, argumentRoots, argumentsAfter,
    resultRoots, after, access, _, _, replay, checked, _, _, _, origins, _, _⟩ := occurrence
  have localModule : localEnv.mod = module := (congrArg AccessEnv.mod access).trans moduleEq
  have localContext : localEnv.ctx = initContext := (congrArg AccessEnv.ctx access).trans contextEq
  obtain ⟨_, sourceRoots, sourceRow, _⟩ := origins index address argumentRow
  have bounded : index < syntaxArgs.length := by
    rw [← AdmittedSourceCalls.rpArgs_length replay]
    exact (List.getElem?_eq_some_iff.mp sourceRow).1
  obtain ⟨declared, nativeRow⟩ : ∃ declared,
      (index, declared) ∈ (lowerContextAt module callee implementation).roots.contents.toList := by
    cases found : (lowerContextAt module callee implementation).roots.contents.find? (·.1 == index) with
    | none => simp [found] at observed
    | some entry =>
      have listFound := found
      rw [← Array.find?_toList] at listFound
      obtain ⟨key, declared⟩ := entry
      have same : key = index := by simpa using List.find?_some listFound
      subst key
      exact ⟨declared, List.mem_of_find?_eq_some listFound⟩
  obtain ⟨parameter, parameterAt, contentRow⟩ := AdmittedSourceCalls.lowerContextAt_content_row_source nativeRow
  have aligned : parameter.var = index :=
    ((validate_modOk module accepted).impl callee.impl implementation implementationRow |>.params index parameter parameterAt).1
  have row : (callee.contentRoots.find? (·.1 == index)).map (·.2) = some declared := by
    simpa only [aligned] using contentRow
  have receiver := checkContents_ok localEnv calleeId syntaxArgs argumentRoots callee checked
    (by simpa only [localModule] using calleeRow) index bounded
  obtain ⟨mapped, _, localReceiver | forwarded⟩ := AdmittedSourceCalls.checkContent_receiver_bounds receiver row
  · obtain ⟨mu, slot, ceiling, _, annotation, _⟩ := localReceiver
    simp [PEnv.ann, localContext, initContext] at annotation
  · obtain ⟨mu, slot, ceiling, _, contents, _⟩ := forwarded
    simp [PEnv.cont, localContext, initContext] at contents

theorem SourceReadyFunction.call_argument_physical (facts : SourceReadyFunction)
    {calleeId : ContextId} {callee : Context} {implementation : Impl}
    {value address : ValueId} {arguments : List ValueId} {origin : Option OriginId} {index : Nat}
    (calleeRow : facts.source.mod.contexts[calleeId]? = some callee)
    (implementationRow : facts.source.mod.impls[callee.impl]? = some implementation)
    (occurrence : CallOccurrence facts.source facts.root facts.func facts.upper value calleeId arguments origin)
    (argumentRow : arguments[index]? = some address)
    (observed : ((lowerContextAt facts.source.mod callee implementation).roots.contents.find? (·.1 == index)).isSome = true) :
    ∃ localEnv place, ReadAddressPhysical localEnv place (rootsAt facts.upper.vals address) := by
  cases facts.caller with
  | global implementation context =>
    exact False.elim (occurrence.no_global_content_receiver facts.accepted rfl context
      calleeRow implementationRow argumentRow observed)
  | context callerId callerRow callerImplementationRow =>
    obtain ⟨localEnv, path, syntaxArgs, sourceOrigin, before, argumentRoots, argumentsAfter,
      resultRoots, after, access, _, _, replay, checked, _, _, _, origins, physical, _⟩ := occurrence
    obtain ⟨_, sourceRoots, sourceRow, _⟩ := origins index address argumentRow
    obtain ⟨mu, place, _, _, _, _, physical⟩ := AdmittedSourceCalls.content_receiver_physical
      facts.accepted callerRow callerImplementationRow calleeRow implementationRow access replay checked
      sourceRow argumentRow observed physical
    exact ⟨localEnv, place, physical⟩

#print axioms CallOccurrence.no_global_content_receiver
#print axioms SourceReadyFunction.call_argument_physical

end Goose.Lower.Validation.ReplacementContentFlowSource
