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

theorem ReplacementSiteAt.prefix_cleared {le : LEnv} {state : LS}
    {index position owner value : Nat} {origin : OriginId}
    (witness : ReplacementSiteAt le state index position owner value origin)
    {module : GIR.Module} {func : Func} {types : Array (Option VTy)} {queries : ReplacementQueries}
    (emitted : EmitsOnly (ReplacementInstApart module types queries owner)
      witness.source.site.cleared witness.source.site.captured)
    (blocks : func.blocks = finishBlocks state.blocks)
    {body : GIR.Block} (row : func.blocks[index]? = some body)
    {head tail : List Inst}
    (split : body.insts = head ++ .eff (.replace owner value (some origin)) :: tail)
    (positionAt : head.length = position) :
    owner ∈ head.foldl (transferEmptyInst module types queries)
      (ReplacementRegionFacts witness.source.site.cleared witness.source.site.captured owner index) := by
  obtain ⟨raw, rest, rawAt, _, rawSplit⟩ := witness.occurrence
  obtain ⟨rawBody, sourceAt, equal⟩ := finishBlocks_row_source blocks row
  have same : rawBody = raw := Option.some.inj (sourceAt.symm.trans rawAt)
  subst rawBody
  have whole : body.insts = witness.capturedBody.insts.toList ++
      .eff (.replace owner value (some origin)) :: rest := by
    rw [← equal]
    exact rawSplit
  have length : witness.capturedBody.insts.toList.length = head.length := by
    simpa only [Array.length_toList] using witness.position_eq.trans positionAt.symm
  have headEqual : head = witness.capturedBody.insts.toList := by
    have taken := congrArg (List.take head.length) (split.symm.trans whole)
    simp only [List.take_append, List.take_length, Nat.sub_self, List.take_zero, List.append_nil] at taken
    simpa only [← length, List.take_length, Nat.sub_self, List.take_zero, List.append_nil] using taken
  rw [headEqual]
  exact witness.current_cleared emitted

#print axioms AcceptedReplacementSite.region_closed
#print axioms ReplacementSiteAt.prefix_cleared
#print axioms ReplacementSiteAt.current_cleared

end Goose.Lower.Validation
