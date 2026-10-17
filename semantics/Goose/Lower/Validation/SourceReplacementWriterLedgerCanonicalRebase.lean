import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalSites
import Goose.Lower.Validation.SourceReplacementLexicalWritersTraversal

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR ReplacementContentFlowSource SourceReplacementLexicalWriters

def SiteOccurrences.withSourcePath {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    {block position owner value : Nat} {origin : OriginId}
    (site : SiteOccurrences env root targets le state func types upper block position owner value origin)
    (path : List Nat)
    (source : DemandNodeAt root path (.statement (.assignWhole site.source.site.source.place site.source.site.source.rhs origin))) :
    SiteOccurrences env root targets le state func types upper block position owner value origin :=
  { site with source := {
      site.source with
      site := { site.source.site with source := {
        site.source.site.source with sourceRoot := root, sourcePath := path, structuralSource := source } }
      root_eq := rfl } }

theorem CanonicalSiteOccurrences.actualSource {ownerRoot : Fragment} {ownerInitial baseline : LS}
    {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    {block position owner value : Nat} {origin : OriginId}
    (canonical : CanonicalSiteOccurrences ownerRoot ownerInitial baseline env root targets le state func types upper
      block position owner value origin)
    (rootEq : ownerRoot.node = root)
    (fresh : ¬ ∃ body, baseline.blocks[block]? = some body ∧
      body.insts[position]? = some (.eff (.replace owner value (some origin)))) :
    ∃ site : SiteOccurrences env root targets le state func types upper block position owner value origin,
      ∃ loop, SourceLoweringAt ownerRoot le ownerInitial site.source.site.source.sourcePath
        (.statement loop (.assignWhole site.source.site.source.place site.source.site.source.rhs origin))
        site.source.site.source.initial := by
  rcases canonical.source with old | actual
  · exact False.elim (fresh old)
  · obtain ⟨path,loop,located⟩ := actual
    have source := sourceLoweringAt_source located
    rw [rootEq] at source
    exact ⟨SiteOccurrences.withSourcePath canonical.site path source,loop,located⟩

theorem CanonicalOccurrenceSitesBuilder.finishBlocks {ownerRoot : Fragment} {ownerInitial baseline : LS}
    {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le state func types upper)
    (rootEq : ownerRoot.node = root) (empty : baseline.insts = [])
    (blocks : func.blocks = finishBlocks state.blocks)
    {blockIndex : Nat} {block : GIR.Block} (row : func.blocks[blockIndex]? = some block)
    {position owner value : Nat} {origin : Option OriginId}
    (present : block.insts[position]? = some (.eff (.replace owner value origin))) :
    ∃ sourceOrigin, origin = some sourceOrigin ∧
      ∃ site : SiteOccurrences env root targets le state func types upper blockIndex position owner value sourceOrigin,
        ∃ loop, SourceLoweringAt ownerRoot le ownerInitial site.source.site.source.sourcePath
          (.statement loop (.assignWhole site.source.site.source.place site.source.site.source.rhs sourceOrigin))
          site.source.site.source.initial := by
  rw [blocks,Goose.Lower.finishBlocks,Array.getElem?_map] at row
  cases bodyRow : state.blocks[blockIndex]? with
  | none => simp [bodyRow] at row
  | some body =>
    simp only [bodyRow,Option.map_some,Option.some.injEq] at row
    subst block
    have authority := checked blockIndex body bodyRow position (.eff (.replace owner value origin))
      (by simpa using present)
    cases origin with
    | none => exact False.elim authority
    | some sourceOrigin =>
      obtain ⟨canonical⟩ := authority
      obtain ⟨site,loop,located⟩ := canonical.actualSource rootEq (by
        rintro ⟨previous,previousRow,previousInst⟩
        have member : Inst.eff (.replace owner value (some sourceOrigin)) ∈ baseline.insts := by
          apply List.mem_flatMap.mpr
          exact ⟨previous,Array.mem_toList_iff.mpr (Array.mem_of_getElem? previousRow),
            Array.mem_toList_iff.mpr (Array.mem_of_getElem? previousInst)⟩
        rw [empty] at member
        contradiction)
      exact ⟨sourceOrigin,rfl,site,loop,located⟩

#print axioms SiteOccurrences.withSourcePath
#print axioms CanonicalSiteOccurrences.actualSource
#print axioms CanonicalOccurrenceSitesBuilder.finishBlocks

end Goose.Lower.Validation.SourceReplacementWriterLedger
