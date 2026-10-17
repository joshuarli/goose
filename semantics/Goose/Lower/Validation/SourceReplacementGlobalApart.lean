import Goose.Lower.Validation.SourceReplacementCallFootprintApart
import Goose.Lower.Validation.SourceReplacementCallContentsApart

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem site_global_rhs_apart_of_accepted {module : Core.Module}
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
    : EmitsOnly (ReplacementInstApart (lower module) ((lowerGlobal module global).init.valueTypes (lower module))
      (replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))) owner)
      site.source.site.source.site.cleared site.source.site.source.site.captured := by
  apply site_global_rhs_apart_of_raw_call_flows accepted globalAt site demand below
  · intro states statesModel final finalAt block member value function arguments callOrigin called chosen notLeaf occurrence
      current within growth
    apply site_global_call_returned_apart_of_contents accepted globalAt site demand below member called occurrence
      statesModel finalAt chosen notLeaf growth within
    intro callee calleeAt index observed reference argument argumentAt
    obtain ⟨context, impl, contextAt, implAt, same⟩ := accepted_function_context accepted calleeAt
    subst callee
    exact site_global_call_content_apart_of_accepted site accepted contextAt implAt occurrence argumentAt observed current
  · intro value block function arguments callOrigin member called occurrence argumentApart final finalAt states statesModel
      effects effectsAt
    apply site_global_call_touched_apart_of_contents accepted globalAt site demand below member called occurrence
      statesModel finalAt effectsAt argumentApart
    intro callee calleeAt index observed reference argument argumentAt
    obtain ⟨context, impl, contextAt, implAt, same⟩ := accepted_function_context accepted calleeAt
    subst callee
    exact site_global_call_content_apart_of_accepted site accepted contextAt implAt occurrence argumentAt observed final

#print axioms site_global_rhs_apart_of_accepted

end Goose.Lower.Validation
