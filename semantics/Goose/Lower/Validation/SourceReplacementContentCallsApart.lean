import Goose.Lower.Validation.SourceReplacementContentRhsApart
import Goose.Lower.Validation.SourceReplacementCallFootprintApart

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem site_rhs_apart_of_final_content {module : Core.Module}
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
    {final : State}
    (finalModel : ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))).model = some final)
    (within : final.ScopedValuesWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper
      site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size)
      (OwnerDependencyApart (lower module) (lowerContextAt module context impl)
        (replacementQueries (lower module) (lowerContextAt module context impl)
          ((lowerContextAt module context impl).valueTypes (lower module))) owner))
    (contents : ∀ value block function arguments callOrigin,
      block ∈ (lowerContextAt module context impl).blocks.toList →
      Inst.def value (.call function arguments callOrigin) ∈ block.insts →
      CallOccurrence site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) upper
        value function arguments callOrigin →
      ∀ callee, (lower module).funcs[function]? = some callee →
      ∀ index, (callee.roots.contents.find? (·.1 == index)).isSome = true →
      (callee.params[index]?).any Ty.isRefSlice = true →
      ∀ argument, arguments[index]? = some argument →
      (content (lowerContextAt module context impl) final (flowAt final.values argument)).AtomsWithin (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner)) :
    EmitsOnly (ReplacementInstApart (lower module) ((lowerContextAt module context impl).valueTypes (lower module))
      (replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))) owner)
      site.source.site.source.site.cleared site.source.site.source.site.captured := by
  apply site_rhs_apart_of_final_scoped_values accepted contextAt implAt site demand below finalModel within
  intro value block function arguments callOrigin member called occurrence argumentApart
  obtain ⟨target, targetAt, ownerKnown⟩ := site_owner_query_of_accepted accepted contextAt implAt site demand below
  apply CallOccurrence.dependencies_apart_of_callRoots demand accepted (congrArg AccessEnv.mod site.access)
    (site.access.trans (demand.access_context contextAt implAt).symm)
    (lowerContext_canonical_facts_of_accepted accepted contextAt implAt) member called occurrence targetAt
    (lowerContextAt_parameterRoots_closed accepted contextAt implAt) ownerKnown argumentApart
  obtain ⟨roots, known⟩ := accepted_context_factory_call_query_known accepted contextAt implAt member called
  rw [known]
  apply function_call_apart_of_public_touches (flow :=
    (replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))) known ?_ ?_
  · intro argument argumentMember
    have bounded := (lowerContextAt_operand_bounds module context impl).1 block member
      (.def value (.call function arguments callOrigin)) called argument argumentMember
    have apart := argumentApart argument argumentMember
    rw [replacementQueries_ownerDependencies _ _ _ _ bounded] at apart
    exact apart
  · intro actual actualAt states statesAt effects effectsAt
    have same : actual = final := Option.some.inj (actualAt.symm.trans finalModel)
    subst actual
    exact site_call_touched_apart_of_contents accepted contextAt implAt site demand below member called occurrence
      statesAt finalModel effectsAt argumentApart (contents value block function arguments callOrigin member called occurrence)

#print axioms site_rhs_apart_of_final_content

end Goose.Lower.Validation
