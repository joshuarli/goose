import Goose.Lower.Validation.ReplacementSourceSitesEvidence
import Goose.Lower.Validation.ReplacementPrefixShape
import Goose.Lower.Validation.ReplacementCurrentRegion

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem AcceptedReplacementSite.region_closed {le : LEnv} {state : LS}
    {owner value : ValueId} {origin : OriginId}
    (witness : AcceptedReplacementSite le state owner value origin)
    {module : GIR.Module} {func : Func} {types : Array (Option VTy)} {queries : ReplacementQueries}
    (emitted : EmitsOnly (ReplacementInstApart module types queries owner) witness.site.cleared witness.site.captured)
    (closed : ∀ body ∈ state.blocks.toList, ClosedBlock body)
    (blocks : func.blocks = finishBlocks state.blocks) :
    EmptyFactsClosed module func types queries
      (ReplacementRegionFacts witness.site.cleared witness.site.captured owner) := by
  have clearRun := witness.site.clearRun
  rw [witness.owner_eq] at clearRun
  exact replacementRegion_closed_of_emission witness.addressed_liveBound clearRun emitted
    (advB_lowerExpr witness.rhs _ _ _ _ witness.site.rhsRun)
    witness.cleared_generated.targets witness.framed witness.captured_extension
    (shaped_of_closed_extension witness.captured_extension closed) closed blocks

theorem ReplacementSiteAt.current_cleared {le : LEnv} {state : LS}
    {block position owner value : Nat} {origin : OriginId}
    (witness : ReplacementSiteAt le state block position owner value origin)
    {module : GIR.Module} {types : Array (Option VTy)} {queries : ReplacementQueries}
    (emitted : EmitsOnly (ReplacementInstApart module types queries owner)
      witness.source.site.cleared witness.source.site.captured) :
    owner ∈ transferEmptyBlock module types queries
      (ReplacementRegionFacts witness.source.site.cleared witness.source.site.captured owner block)
      (cfgBlock witness.capturedBody) := by
  have clearRun := witness.source.site.clearRun
  rw [witness.source.owner_eq] at clearRun
  exact replacementRegion_current_contains witness.source.addressed_liveBound clearRun emitted
    (advB_lowerExpr witness.source.rhs _ _ _ _ witness.source.site.rhsRun) witness.current witness.row

#print axioms AcceptedReplacementSite.region_closed
#print axioms ReplacementSiteAt.current_cleared

end Goose.Lower.Validation
