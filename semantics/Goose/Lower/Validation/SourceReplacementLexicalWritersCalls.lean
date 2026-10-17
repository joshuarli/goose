import Goose.Lower.Validation.SourceReplacementLexicalWritersSlotInit
import Goose.Lower.Validation.SourceReplacementLexicalWritersCallReceivers
import Goose.Lower.Validation.SourceReadyCanonicalInputs
import Goose.Lower.Validation.SourceReadyCallPhysical

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core Goose.Core.Sound Goose.GIR SourceReplacementWriterLedger SourceReplacementWriterTyping
open ReplacementContentFlowSource

section Context

variable {module : Core.Module} {context : Context} {impl : Impl} {contextIndex : ContextId}
  {env : PEnv} {root : DemandNode} {targets : List BlockId}
  {types : Array (Option VTy)} {upper : Prov}
  {blockIndex sitePosition owner replacementValue : Nat} {origin : OriginId}
  (site : SiteOccurrences env root targets
    (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
    (lowerContextAt module context impl) types upper blockIndex sitePosition owner replacementValue origin)

theorem context_observed_call_interval_of_accepted
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {replacementPath rhsPath : List Nat}
    (source : DemandNodeAt (.block impl.body) replacementPath
      (.statement (.assignWhole site.source.site.source.place site.source.site.source.rhs origin)))
    (demand : ReplacementDemandContext module contextIndex replacementPath
      site.source.site.source.place site.source.site.source.rhs origin)
    (rhsAt : SourceLoweringAt (contextFragment module impl) (lowerEnv module impl.vars impl.results.toList)
      (contextInitial module impl) rhsPath (.expression site.source.site.source.rhs)
      site.source.site.source.site.cleared)
    {tracked : VarId} {localVar : LocalVar} (variableAt : impl.vars[tracked]? = some localVar)
    (used : tracked ∈ site.source.site.source.rhs.variables)
    (inactive : tracked ∉ demand.statement.expected.frame.active)
    {block : GIR.Block} (blockMember : block ∈ (lowerContextAt module context impl).blocks.toList)
    {value function : Nat} {arguments : List ValueId} {callOrigin : Option OriginId}
    (instMember : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    {callee : Context} {calleeImpl : Impl}
    (calleeAt : module.contexts[function]? = some callee)
    (calleeImplAt : module.impls[callee.impl]? = some calleeImpl)
    {index argument : Nat} (argumentAt : arguments[index]? = some argument)
    (reference : ((lowerContextAt module callee calleeImpl).params[index]?).any Ty.isRefSlice = true)
    (observed : ((lowerContextAt module callee calleeImpl).roots.contents.find? (·.1 == index)).isSome = true)
    (trackedMember : RootRef.local tracked ∈ rootsAt
      ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount).vals argument) :
    site.source.site.source.site.cleared.vals.size ≤ value ∧
      value < site.source.site.source.site.captured.vals.size := by
  obtain ⟨facts,sourceEq,rootEq,functionEq,typesEq,provenanceEq,completedEq,_⟩ :=
    accepted_context_ready_inputs accepted contextAt implAt
  have actualBlock : block ∈ facts.func.blocks.toList := by rw [functionEq]; exact blockMember
  have occurrence := (facts.occurrences _ actualBlock _ instMember).2.2.1 value function arguments callOrigin rfl
  obtain ⟨physicalEnv,physicalPlace,physical⟩ := facts.call_argument_physical
    (by simpa only [sourceEq] using calleeAt) (by simpa only [sourceEq] using calleeImplAt)
    occurrence argumentAt (by simpa only [sourceEq] using observed)
  obtain ⟨callFacts⟩ := facts.native.calls _ actualBlock value function arguments callOrigin instMember
  have nativeReference := call_refSlice_argument_reference callFacts
    (by simpa only [sourceEq] using lower_func_at calleeAt calleeImplAt) argumentAt reference
  obtain ⟨path,fragment,before,event,typing,scopes,located,member,same,stack,
    moduleEq,varsEq,implEq,scopesEq,visible,typed,bounded,eventBound,eventRun,eventFirst,eventLast,eventContinuation⟩ :=
    context_native_writer accepted implAt blockMember instMember (by trivial)
  obtain ⟨syntaxArgs,sourceOrigin,rfl,originEq,argumentsRun,emissionRun⟩ :=
    Fragment.call_emission_shape member same
  obtain ⟨callType,start,finish,callTyped⟩ := typed.call
  have tables : SourceRootTables typing facts.source := by
    constructor
    · simpa only [sourceEq] using moduleEq.symm
    · simpa only [sourceEq] using varsEq.symm
  have rootExtension :
      ((contextFragment module impl).finish (lowerEnv module impl.vars impl.results.toList)
        (contextInitial module impl)).Ext (cfg_implState module impl) := by
    rw [contextFragment_finish]
    exact (advB_finishFunction _ _ _ _ _ _ rfl).ext
  have argumentsExtension : event.before.Ext facts.completed := by
    rw [completedEq]
    exact (adv_emitDef emissionRun).ext.trans (eventLast.trans (located.span.2.trans rootExtension))
  have actualRun : lowerArgs syntaxArgs (lowerEnv typing.mod typing.vars impl.results.toList) before =
      (arguments,event.before) := by rw [moduleEq,varsEq]; exact argumentsRun
  have actualTracked : RootRef.local tracked ∈ rootsAt facts.provenance.vals argument := by
    rw [provenanceEq]
    exact trackedMember
  have live : event.before.cur.isSome = true := eventRun.1
  obtain ⟨argumentSyntax,trackedVisible⟩ := typed_call_local_holder_visible facts tables callTyped
    (by simpa only [sourceEq] using calleeAt) (by simpa only [sourceEq] using calleeImplAt)
    (by simpa only [sourceEq] using reference) bounded actualRun argumentAt live argumentsExtension
    nativeReference physical actualTracked
  have nested := inactive_rhs_visible_writer_prefix accepted contextAt implAt source demand
    (by rfl) rhsAt located stack varsEq visible variableAt used inactive trackedVisible
  exact canonical_writer_call_result_interval site rhsAt located nested member same

theorem context_call_interval_of_accepted
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {replacementPath rhsPath : List Nat}
    (source : DemandNodeAt (.block impl.body) replacementPath
      (.statement (.assignWhole site.source.site.source.place site.source.site.source.rhs origin)))
    (demand : ReplacementDemandContext module contextIndex replacementPath
      site.source.site.source.place site.source.site.source.rhs origin)
    (rhsAt : SourceLoweringAt (contextFragment module impl) (lowerEnv module impl.vars impl.results.toList)
      (contextInitial module impl) rhsPath (.expression site.source.site.source.rhs)
      site.source.site.source.site.cleared)
    {tracked : VarId} {localVar : LocalVar} (variableAt : impl.vars[tracked]? = some localVar)
    (used : tracked ∈ site.source.site.source.rhs.variables)
    (inactive : tracked ∉ demand.statement.expected.frame.active)
    {block : GIR.Block} (blockMember : block ∈ (lowerContextAt module context impl).blocks.toList)
    {value function : Nat} {arguments : List ValueId} {callOrigin : Option OriginId}
    (instMember : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    {callee : Func} (calleeAt : (lower module).funcs[function]? = some callee)
    {index argument : Nat} (argumentAt : arguments[index]? = some argument)
    (reference : (callee.params[index]?).any Ty.isRefSlice = true)
    (observed : (callee.roots.contents.find? (·.1 == index)).isSome = true)
    (trackedMember : RootRef.local tracked ∈ rootsAt
      ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount).vals argument) :
    site.source.site.source.site.cleared.vals.size ≤ value ∧
      value < site.source.site.source.site.captured.vals.size := by
  have bound : function < module.contexts.size := by
    simpa only [lower,Array.size_map] using (Array.getElem?_eq_some_iff.mp calleeAt).1
  have sourceAt := Array.getElem?_eq_getElem bound
  obtain ⟨sourceImpl,sourceImplAt,_⟩ := (validate_modOk module accepted).ctx function _ sourceAt
  have same : callee = lowerContextAt module module.contexts[function] sourceImpl :=
    Option.some.inj (calleeAt.symm.trans (lower_func_at sourceAt sourceImplAt))
  subst callee
  exact context_observed_call_interval_of_accepted site accepted contextAt implAt source demand rhsAt
    variableAt used inactive blockMember instMember sourceAt sourceImplAt argumentAt reference observed trackedMember

end Context

#print axioms context_call_interval_of_accepted
#print axioms context_observed_call_interval_of_accepted

end Goose.Lower.Validation.SourceReplacementLexicalWriters
