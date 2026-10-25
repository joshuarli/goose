import Goose.Lower.Validation.SourceReplacementLexicalWritersTraversal
import Goose.Lower.Validation.SourceReplacementLexicalWritersEmissionIntervals

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core Goose.GIR SourceReplacementWriterLedger

section Context

variable {module : Core.Module} {context : Context} {impl : Impl}
  {env : PEnv} {root : DemandNode} {targets : List BlockId}
  {types : Array (Option VTy)} {upper : Prov}
  {blockIndex sitePosition owner replacementValue : Nat} {origin : OriginId}
  (site : ReplacementContentFlowSource.SiteOccurrences env root targets
    (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
    (lowerContextAt module context impl) types upper blockIndex sitePosition owner replacementValue origin)

variable {ownerRoot writer : Fragment} {initial writerBefore : LS}
  {rhsPath writerPath : List Nat}
  (rhsAt : SourceLoweringAt ownerRoot (lowerEnv module impl.vars impl.results.toList) initial rhsPath
    (.expression site.source.site.source.rhs) site.source.site.source.site.cleared)
  (writerAt : SourceLoweringAt ownerRoot (lowerEnv module impl.vars impl.results.toList) initial writerPath
    writer writerBefore)
  (nested : rhsPath <+: writerPath)

include rhsAt writerAt nested

theorem canonical_writer_bounds : LiveBound writerBefore ∧
    site.source.site.source.site.cleared.Ext writerBefore ∧
    (writer.finish (lowerEnv module impl.vars impl.results.toList) writerBefore).Ext
      site.source.site.source.site.captured := by
  obtain ⟨suffix, _, localAt⟩ := sourceLoweringAt_descendant rhsAt writerAt nested
  have bounded := localAt.liveBound site.source.site.source.cleared_generated.live
  have spans := localAt.span
  have finish : (Fragment.expression site.source.site.source.rhs).finish
      (lowerEnv module impl.vars impl.results.toList) site.source.site.source.site.cleared =
      site.source.site.source.site.captured :=
    congrArg Prod.snd site.source.site.source.site.rhsRun
  rw [finish] at spans
  exact ⟨bounded, spans⟩

theorem canonical_writer_slotInit_source_interval {emission : Emission} {slot source : Nat}
    {sourceOrigin : Option OriginId}
    (member : emission ∈ writer.emissions (lowerEnv module impl.vars impl.results.toList) writerBefore)
    (instruction : emission.instruction = .eff (.slotInit slot source sourceOrigin)) :
    site.source.site.source.site.cleared.vals.size ≤ source ∧
      source < site.source.site.source.site.captured.vals.size := by
  obtain ⟨bounded, first, last⟩ := canonical_writer_bounds site rhsAt writerAt nested
  exact canonical_slotInit_source_interval site bounded member instruction first last

theorem canonical_writer_store_source_interval {emission : Emission} {address source : Nat}
    {sourceOrigin : Option OriginId}
    (member : emission ∈ writer.emissions (lowerEnv module impl.vars impl.results.toList) writerBefore)
    (instruction : emission.instruction = .eff (.store address source sourceOrigin)) :
    site.source.site.source.site.cleared.vals.size ≤ source ∧
      source < site.source.site.source.site.captured.vals.size := by
  obtain ⟨bounded, first, last⟩ := canonical_writer_bounds site rhsAt writerAt nested
  exact canonical_store_source_interval site bounded member instruction first last

theorem canonical_writer_call_result_interval {emission : Emission} {value function : Nat}
    {arguments : List ValueId} {callOrigin : Option OriginId}
    (member : emission ∈ writer.emissions (lowerEnv module impl.vars impl.results.toList) writerBefore)
    (instruction : emission.instruction = .def value (.call function arguments callOrigin)) :
    site.source.site.source.site.cleared.vals.size ≤ value ∧
      value < site.source.site.source.site.captured.vals.size := by
  obtain ⟨bounded, first, last⟩ := canonical_writer_bounds site rhsAt writerAt nested
  exact canonical_call_result_interval site bounded member instruction first last

end Context

#print axioms canonical_writer_bounds
#print axioms canonical_writer_slotInit_source_interval
#print axioms canonical_writer_store_source_interval
#print axioms canonical_writer_call_result_interval

end Goose.Lower.Validation.SourceReplacementLexicalWriters
