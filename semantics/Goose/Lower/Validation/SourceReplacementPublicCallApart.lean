import Goose.Lower.Validation.SourceReplacementCallQueriesApart
import Goose.Lower.Validation.ReplacementOccurrenceCallDependenciesApart

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem site_rhs_apart_of_public_call_queries {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, impl, context, []⟩ (.block impl.body) []
      (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module contextIndex
      site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount) upper)
    (callTransfer : ∀ states, (replacementContentFlow (lower module)).model = some states →
      ∀ final, ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).model = some final →
      ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ value function arguments callOrigin,
      Inst.def value (.call function arguments callOrigin) ∈ block.insts →
      ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
        (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper
        site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size value →
      ¬ ScopedDemandLeaf site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper value →
      CallOccurrence site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) upper
        value function arguments callOrigin →
      ∀ current, current.ScopedValuesWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
        (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper
        site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) (OwnerDependencyApart (lower module) (lowerContextAt module context impl)
          (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) → current.Extends final →
        ((callState (lower module) states (lowerContextAt module context impl) current function arguments).1).AtomsWithin (OwnerDependencyApart (lower module) (lowerContextAt module context impl)
          (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner))
    (publicCalls : ∀ value block callee args callOrigin,
      block ∈ (lowerContextAt module context impl).blocks.toList →
      Inst.def value (.call callee args callOrigin) ∈ block.insts →
      CallOccurrence site.localEnv (.expression site.source.site.source.rhs)
        (lowerContextAt module context impl) upper value callee args callOrigin →
      (∀ argument ∈ args,
        ReplacementApart (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner
          ((replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).ownerDependencies argument)) →
      ReplacementApart (replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))) owner
        ((replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).callRoots callee args)) :
    EmitsOnly (ReplacementInstApart (lower module) ((lowerContextAt module context impl).valueTypes (lower module))
      (replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))) owner)
      site.source.site.source.site.cleared site.source.site.source.site.captured := by
  apply site_rhs_apart_of_call_queries accepted contextAt implAt site demand below callTransfer
  intro value block callee args callOrigin member called occurrence argumentApart
  obtain ⟨target, targetAt, ownerKnown⟩ := site_owner_query_of_accepted accepted contextAt implAt site demand below
  exact CallOccurrence.dependencies_apart_of_callRoots demand accepted (congrArg AccessEnv.mod site.access) (site.access.trans (demand.access_context contextAt implAt).symm)
    (lowerContext_canonical_facts_of_accepted accepted contextAt implAt) member called occurrence targetAt
    (lowerContextAt_parameterRoots_closed accepted contextAt implAt) ownerKnown argumentApart
    (publicCalls value block callee args callOrigin member called occurrence argumentApart)

theorem site_global_rhs_apart_of_public_call_queries {module : Core.Module}
    {globalIndex : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[globalIndex]? = some global)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, Core.initImpl, Core.initContext, []⟩ (.expression global.init) []
      (lowerEnv module #[] [global.ty]) (cfg_globalState module global)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module (module.contexts.size + globalIndex)
      site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerGlobal module global).init.provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount) upper)
    (callTransfer : ∀ states, (replacementContentFlow (lower module)).model = some states →
      ∀ final, ((replacementContentFlow (lower module)).forFunction (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))).model = some final →
      ∀ block ∈ (lowerGlobal module global).init.blocks.toList, ∀ value function arguments callOrigin,
      Inst.def value (.call function arguments callOrigin) ∈ block.insts →
      ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
        (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper
        site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size value →
      ¬ ScopedDemandLeaf site.localEnv (.expression site.source.site.source.rhs) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper value →
      CallOccurrence site.localEnv (.expression site.source.site.source.rhs) (lowerGlobal module global).init upper
        value function arguments callOrigin →
      ∀ current, current.ScopedValuesWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
        (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper
        site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) (OwnerDependencyApart (lower module) (lowerGlobal module global).init
          (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner) → current.Extends final →
        ((callState (lower module) states (lowerGlobal module global).init current function arguments).1).AtomsWithin (OwnerDependencyApart (lower module) (lowerGlobal module global).init
          (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner))
    (publicCalls : ∀ value block callee args callOrigin,
      block ∈ (lowerGlobal module global).init.blocks.toList →
      Inst.def value (.call callee args callOrigin) ∈ block.insts →
      CallOccurrence site.localEnv (.expression site.source.site.source.rhs)
        (lowerGlobal module global).init upper value callee args callOrigin →
      (∀ argument ∈ args,
        ReplacementApart (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner
          ((replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))).ownerDependencies argument)) →
      ReplacementApart (replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))) owner
        ((replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))).callRoots callee args)) :
    EmitsOnly (ReplacementInstApart (lower module) ((lowerGlobal module global).init.valueTypes (lower module))
      (replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))) owner)
      site.source.site.source.site.cleared site.source.site.source.site.captured := by
  apply site_global_rhs_apart_of_call_queries accepted globalAt site demand below callTransfer
  intro value block callee args callOrigin member called occurrence argumentApart
  obtain ⟨target, targetAt, ownerKnown⟩ := site_global_owner_query_of_accepted accepted globalAt site demand below
  exact CallOccurrence.dependencies_apart_of_callRoots demand accepted (congrArg AccessEnv.mod site.access) (site.access.trans demand.access_global.symm)
    (lowerGlobal_canonical_facts_of_accepted accepted globalAt) member called occurrence targetAt
    (global_initializer_parameterRoots_closed module global) ownerKnown argumentApart
    (publicCalls value block callee args callOrigin member called occurrence argumentApart)

#print axioms site_rhs_apart_of_public_call_queries
#print axioms site_global_rhs_apart_of_public_call_queries

end Goose.Lower.Validation
