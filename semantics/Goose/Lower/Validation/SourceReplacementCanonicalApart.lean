import Goose.Lower.Validation.SourceReplacementContentTransfersApart
import Goose.Lower.Validation.SourceReplacementLexicalWritersSlotInit
import Goose.Lower.Validation.SourceReplacementLexicalWritersCalls
import Goose.Lower.Validation.SourceReplacementLexicalWritersStoreInterval

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open SourceReplacementWriterLedger SourceReplacementLexicalWriters

theorem site_rhs_apart_of_canonical_cursor {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, impl, context, []⟩ (.block impl.body) []
      (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module contextIndex site.source.site.source.sourcePath
      site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount) upper)
    {rhsPath : List Nat}
    (cursor : SourceLoweringAt (contextFragment module impl) (lowerEnv module impl.vars impl.results.toList)
      (contextInitial module impl) rhsPath (.expression site.source.site.source.rhs)
      site.source.site.source.site.cleared) :
    EmitsOnly (ReplacementInstApart (lower module) ((lowerContextAt module context impl).valueTypes (lower module))
      (replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))) owner)
      site.source.site.source.site.cleared site.source.site.source.site.captured := by
  have source : DemandNodeAt (.block impl.body) site.source.site.source.sourcePath
      (.statement (.assignWhole site.source.site.source.place site.source.site.source.rhs origin)) := by
    simpa only [site.source.root_eq] using site.source.site.source.structuralSource
  apply site_rhs_apart_of_localized_writers accepted contextAt implAt site demand below
  · intro block member value function arguments callOrigin called callee calleeAt index argument observed reference argumentAt slot selected rootAt
    obtain ⟨localVar, row, slice, used, inactive⟩ := selected
    exact context_call_interval_of_accepted site accepted contextAt implAt source demand cursor
      row used inactive member called calleeAt argumentAt reference observed rootAt
  · intro block member slot value sourceOrigin initialized selected
    obtain ⟨localVar, row, slice, used, inactive⟩ := selected
    exact context_slotInit_interval_of_accepted site accepted contextAt implAt source demand cursor
      row used inactive member initialized
  · intro block member address value sourceOrigin stored reference slot selected rootAt
    obtain ⟨localVar, row, slice, used, inactive⟩ := selected
    exact context_store_interval_of_accepted site accepted contextAt implAt source demand cursor
      row used inactive member stored reference rootAt

#print axioms site_rhs_apart_of_canonical_cursor

end Goose.Lower.Validation
