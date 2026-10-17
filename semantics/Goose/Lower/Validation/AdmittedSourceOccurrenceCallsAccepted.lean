import Goose.Lower.Validation.AdmittedSourceCallsNativeContents
import Goose.Lower.Validation.AdmittedSourceCallsAccepted
import Goose.Lower.Validation.AdmittedSourceCallTraceTypes
import Goose.Lower.Validation.AdmittedSourceCallsCoverage
import Goose.Lower.Validation.AdmittedSourceCallsObserved
import Goose.Lower.Validation.SourceCanonicalRootFloorsCallTrace
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLedger
import Goose.Lower.Validation.SummaryPreservationEffects

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR ReplacementContentFlowSource SummaryPreservation

private theorem annotation_member {rows : List (Nat × List RootRef)} {index : Nat}
    {roots : List RootRef} (found : (rows.find? (·.1 == index)).map (·.2) = some roots) :
    (index, roots) ∈ rows := by
  cases rowAt : rows.find? (·.1 == index) with
  | none => simp [rowAt] at found
  | some row =>
      have key : row.1 = index := eq_of_beq (List.find?_some (p := fun entry : Nat × List RootRef => entry.1 == index) (a := row) rowAt)
      have value : row.2 = roots := by simpa only [rowAt, Option.map_some, Option.some.injEq] using found
      simpa only [← key, ← value] using List.mem_of_find?_eq_some rowAt

theorem ReplacementContentFlowSource.CallOccurrence.admitted_context
    {module : Core.Module} {caller : Context} {callerImpl : Impl} {callerId : ContextId}
    {env : PEnv} {root : DemandNode} {upper : Prov} {value calleeId : Nat}
    {arguments : List ValueId} {origin : Option OriginId}
    (accepted : Core.validate module = .ok ())
    (callerAt : module.contexts[callerId]? = some caller)
    (callerImplAt : module.impls[caller.impl]? = some callerImpl)
    (occurrence : CallOccurrence env root (lowerContextAt module caller callerImpl) upper value calleeId arguments origin)
    (access : env.access = ⟨module, callerImpl, caller⟩)
    (below : ProvenanceBelow ((lowerContextAt module caller callerImpl).provenance
      (resultRoots (lower module) (lower module).implTypes)
      ((lowerContextAt module caller callerImpl).valueTypes (lower module)) (lower module).rootCount) upper)
    (types : Array (Option VTy)) :
    (lowerContextAt module caller callerImpl).admittedInstruction (lower module) types
      ((lowerContextAt module caller callerImpl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module caller callerImpl).valueTypes (lower module)) (lower module).rootCount)
      (.def value (.call calleeId arguments origin)) = true := by
  let func := lowerContextAt module caller callerImpl
  let provenance := func.provenance (resultRoots (lower module) (lower module).implTypes)
    (func.valueTypes (lower module)) (lower module).rootCount
  change func.admittedInstruction (lower module) types provenance _ = true
  obtain ⟨localEnv, path, syntaxArgs, sourceOrigin, before, argumentRoots, argumentsAfter,
    resultRoots, after, localAccess, originEq, node, argumentsReplay, contentChecked, callReplay,
    valueBound, valueRefined, argumentOrigins, physicalArguments, trace⟩ := occurrence
  cases localEnv with
  | mk actualModule actualImpl actualContext scopes =>
    have identity : actualModule = module ∧ actualImpl = callerImpl ∧ actualContext = caller := by
      simpa only [PEnv.access, AccessEnv.mk.injEq] using localAccess.trans access
    rcases identity with ⟨moduleIdentity, implementationIdentity, contextIdentity⟩
    subst actualModule
    subst actualImpl
    subst actualContext
    have traced := trace
    obtain ⟨returnTypes, initial, final, siteRoot, sourcePath, run, generated, live, continuation,
      location, valid, projects, typing, start, finish, type, moduleEq, variablesEq, source⟩ := traced
    obtain ⟨callee, calleeImpl, argsStart, argsFinish, resultStart,
      calleeAt, calleeImplAt, arity, typedArgs, _⟩ := tyExpr_call_tables source
    rw [moduleEq] at calleeAt calleeImplAt
    have floors := SourceCanonicalRootFloors.lowerContext_callArgumentsTrace_canonical_floor
      accepted callerAt callerImplAt scopes trace argumentsReplay
    have closed := SummaryPreservation.lowerContextAt_parameterRoots_closed accepted callerAt callerImplAt
    apply AdmittedSourceCalls.admittedInstruction_call_of_source_bounds
      (lower_func_at calleeAt calleeImplAt) closed
    intro parameter declared row reference
    obtain ⟨formal, formalAt, sourceAnnotation⟩ := AdmittedSourceCalls.lowerContextAt_content_row_source row
    have parameterBound := (Array.getElem?_eq_some_iff.mp formalAt).1
    have rootsBound : parameter < argumentRoots.length := by
      rw [AdmittedSourceCalls.rpArgs_length argumentsReplay, ← arity]
      simpa using parameterBound
    let sourceRoots := argumentRoots[parameter]
    have sourceRootsAt : argumentRoots[parameter]? = some sourceRoots := by simp [sourceRoots, rootsBound]
    obtain ⟨address, addressAt, addressFloor⟩ := floors parameter sourceRoots sourceRootsAt
    change sourceRoots ⊆ rootsAt provenance.vals address at addressFloor
    obtain ⟨mapped, mappedChecked, receiver⟩ := AdmittedSourceCalls.checkContents_native_row_receiver_bounds
      accepted calleeAt calleeImplAt rfl contentChecked (by simpa using arity.symm) row
    refine ⟨argumentRoots, mapped, mappedChecked, ?_, ?_, ?_⟩
    · intro index argument roots _ argumentAt sourceAt
      obtain ⟨bound, actual, actualAt, refined⟩ := argumentOrigins index argument argumentAt
      have same : actual = roots := Option.some.inj (actualAt.symm.trans sourceAt)
      subst actual
      exact GIR.RootsRefine.actual_mono refined (fun {root} member => below.vals argument root member)
    · intro index roots _ sourceAt
      obtain ⟨argument, argumentAt, floor⟩ := floors index roots sourceAt
      exact ⟨argument, argumentAt, floor⟩
    · rw [List.getElem!_of_getElem? addressAt]
      rcases receiver with localReceiver | parameterReceiver
      · obtain ⟨mutability, slot, ceiling, syntaxAt, annotation, lower, upperBound⟩ := localReceiver
        have physical := physicalArguments parameter address (.byRef mutability (.var slot)) addressAt syntaxAt
          mutability (.var slot) rfl ⟨slot, .inl rfl⟩
        have exactUpper : rootsAt upper.vals address = [.local slot] := by
          cases physical with
          | «local» index same roots => cases same; exact roots
          | contents index same _ _ => cases same
        obtain ⟨childBefore, childAfter, replay⟩ :=
          AdmittedSourceCalls.rpArgs_argument_replay syntaxAt argumentsReplay sourceRootsAt
        have sourceEq : sourceRoots = [.local slot] := by
          exact congrArg Prod.fst ((st_pure_ok _ _ _).mp replay)
        obtain ⟨storage, storageAt, storageReference, ordinary⟩ :=
          AdmittedSourceCalls.trace_refSlice_local_argument accepted calleeAt calleeImplAt rfl
            trace formalAt reference syntaxAt
        have bounds := AdmittedSourceCalls.accepted_slot_ceiling_bounds accepted callerAt callerImplAt
          storageAt storageReference ordinary (annotation_member annotation)
        refine ⟨⟨.local slot, addressFloor (by simp [sourceEq])⟩, ?_, ?_⟩
        · intro receiverRoot member
          have same := List.mem_singleton.mp (exactUpper ▸ below.vals address _ member)
          subst receiverRoot
          exact bounds.1.source_mono upperBound
        · intro receiverRoot member
          have same := List.mem_singleton.mp (exactUpper ▸ below.vals address _ member)
          subst receiverRoot
          exact fun root member => bounds.2 (lower member)
      · obtain ⟨mutability, parameterVar, ceiling, syntaxAt, contents, lower, upperBound⟩ := parameterReceiver
        have sourceReference := AdmittedSourceCalls.accepted_content_reference accepted callerAt callerImplAt rfl contents
        have physical := physicalArguments parameter address
          (.byRef mutability (.deref (.read (.var parameterVar)))) addressAt syntaxAt mutability
          (.deref (.read (.var parameterVar))) rfl
          ⟨parameterVar, .inr ⟨rfl, sourceReference, by simp [contents]⟩⟩
        have exactUpper : rootsAt upper.vals address = [.param parameterVar] := by
          cases physical with
          | «local» index same _ => cases same
          | contents index same _ roots => cases same; exact roots
        cases storageAt : callerImpl.vars[parameterVar]? with
        | none => simp [PEnv.isRefSliceVar, storageAt] at sourceReference
        | some storage =>
          have storageReference : storage.ty.isRefSlice = true := by
            simpa [PEnv.isRefSliceVar, storageAt] using sourceReference
          obtain ⟨callerFormal, callerFormalAt, aligned, _⟩ :=
            SummaryPreservation.accepted_refSlice_parameter accepted callerImplAt storageAt storageReference
          have nativeReference : (func.params[parameterVar]?).any Ty.isRefSlice = true := by
            simp [func, lowerContextAt, lowerImpl, lowerImplFromState, List.getElem?_map,
              Array.getElem?_toList, callerFormalAt, tyOfVar, aligned, storageAt, storageReference]
          have nativeContents : func.contentRoots parameterVar = ceiling := by
            exact AdmittedSourceCalls.lowerContextAt_contentRoots_eq callerFormalAt
              (by simpa only [aligned, PEnv.cont] using contents)
          obtain ⟨_, _, callerChecked⟩ := (validate_modOk module accepted).ctx callerId caller callerAt
          have selfAnnotation := (callerChecked.content parameterVar ceiling contents).2.1
          obtain ⟨childBefore, childAfter, replay⟩ :=
            AdmittedSourceCalls.rpArgs_argument_replay syntaxAt argumentsReplay sourceRootsAt
          have storageRefLike : storage.ty.isRefLike = true := by
            cases shape : storage.ty <;> simp_all only [Ty.isRefSlice, Bool.false_eq_true, Ty.isRefLike]
          have sourceEq : sourceRoots = [.param parameterVar] := by
            change readRoots _ (.var parameterVar) childBefore = .ok (sourceRoots, childAfter) at replay
            simp only [readRoots, storageAt, storageRefLike, ite_true, PEnv.ann, selfAnnotation] at replay
            exact congrArg Prod.fst ((st_pure_ok _ _ _).mp replay)
          have bounds := AdmittedSourceCalls.parameter_receiver_source_bounds
            (provenance := provenance) nativeReference nativeContents lower upperBound
          refine ⟨⟨.param parameterVar, addressFloor (by simp [sourceEq])⟩, ?_, ?_⟩
          · intro receiverRoot member
            have same := List.mem_singleton.mp (exactUpper ▸ below.vals address _ member)
            subst receiverRoot
            exact bounds.1
          · intro receiverRoot member
            have same := List.mem_singleton.mp (exactUpper ▸ below.vals address _ member)
            subst receiverRoot
            exact bounds.2

theorem ReplacementContentFlowSource.CallOccurrence.admitted_global
    {module : Core.Module} {global : Core.Global} {env : PEnv} {root : DemandNode}
    {upper provenance : Prov} {value calleeId : Nat} {arguments : List ValueId} {origin : Option OriginId}
    (accepted : Core.validate module = .ok ())
    (occurrence : CallOccurrence env root (lowerGlobal module global).init upper value calleeId arguments origin)
    (access : env.access = ⟨module, initImpl, initContext⟩)
    (types : Array (Option VTy)) :
    (lowerGlobal module global).init.admittedInstruction (lower module) types provenance
      (.def value (.call calleeId arguments origin)) = true := by
  obtain ⟨localEnv, path, syntaxArgs, sourceOrigin, before, argumentRoots, argumentsAfter,
    resultRoots, after, localAccess, originEq, node, argumentsReplay, contentChecked, callReplay,
    valueBound, valueRefined, argumentOrigins, physicalArguments, trace⟩ := occurrence
  cases localEnv with
  | mk actualModule actualImpl actualContext scopes =>
    have identity : actualModule = module ∧ actualImpl = initImpl ∧ actualContext = initContext := by
      simpa only [PEnv.access, AccessEnv.mk.injEq] using localAccess.trans access
    rcases identity with ⟨moduleIdentity, implementationIdentity, contextIdentity⟩
    subst actualModule
    subst actualImpl
    subst actualContext
    obtain ⟨returnTypes, initial, final, siteRoot, sourcePath, run, generated, live, continuation,
      location, valid, projects, typing, start, finish, type, moduleEq, variablesEq, source⟩ := trace
    obtain ⟨callee, calleeImpl, argsStart, argsFinish, resultStart,
      calleeAt, calleeImplAt, arity, typedArgs, _⟩ := tyExpr_call_tables source
    rw [moduleEq] at calleeAt calleeImplAt
    simp only [Func.admittedInstruction, lower_func_at calleeAt calleeImplAt, List.all_eq_true]
    rintro ⟨parameter, declared⟩ row
    obtain ⟨mapped, mappedChecked, receiver⟩ := AdmittedSourceCalls.checkContents_native_row_receiver_bounds
      accepted calleeAt calleeImplAt rfl contentChecked (by simpa using arity.symm) row
    rcases receiver with ⟨mutability, slot, ceiling, syntaxAt, annotation, lower, upperBound⟩ |
      ⟨mutability, parameterVar, ceiling, syntaxAt, contents, lower, upperBound⟩
    · simp [PEnv.ann, initContext] at annotation
    · simp [PEnv.cont, initContext] at contents

#print axioms ReplacementContentFlowSource.CallOccurrence.admitted_global

#print axioms ReplacementContentFlowSource.CallOccurrence.admitted_context

end Goose.Lower.Validation
