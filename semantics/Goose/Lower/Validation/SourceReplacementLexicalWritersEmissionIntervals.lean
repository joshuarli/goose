import Goose.Lower.Validation.SourceReplacementLexicalWritersEmissionSpans
import Goose.Lower.Validation.SourceReplacementLexicalWritersIntervals

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core Goose.GIR SourceReplacementWriterLedger

theorem emission_current_block {fragment : Fragment} {env : LEnv} {before : LS} {emission : Emission}
    (bounded : LiveBound before) (member : emission ∈ fragment.emissions env before) :
    ∃ index body, emission.before.cur = some index ∧ emission.before.blocks[index]? = some body := by
  have current := (Fragment.emission_run member).1
  have valid := fragment_emission_liveBound bounded member
  cases row : emission.before.cur with
  | none => simp [row] at current
  | some index =>
    have bound := valid index row
    exact ⟨index,emission.before.blocks[index],rfl,by simp [bound]⟩

section Context

variable {module : Core.Module} {context : Context} {impl : Impl}
  {env : PEnv} {root : DemandNode} {targets : List BlockId}
  {types : Array (Option VTy)} {upper : Prov}
  {blockIndex sitePosition owner replacementValue : Nat} {origin : OriginId}
  (site : ReplacementContentFlowSource.SiteOccurrences env root targets
    (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
    (lowerContextAt module context impl) types upper blockIndex sitePosition owner replacementValue origin)

theorem canonical_effect_operand_interval {fragment : Fragment} {before : LS} {emission : Emission}
    {effect : Effect} (bounded : LiveBound before)
    (member : emission ∈ fragment.emissions (lowerEnv module impl.vars impl.results.toList) before)
    (instruction : emission.instruction = .eff effect)
    (initial : site.source.site.source.site.cleared.Ext before)
    (retained : (fragment.finish (lowerEnv module impl.vars impl.results.toList) before).Ext
      site.source.site.source.site.captured) :
    ∀ value ∈ effect.uses, site.source.site.source.site.cleared.vals.size ≤ value ∧
      value < site.source.site.source.site.captured.vals.size := by
  obtain ⟨index,body,live,row⟩ := emission_current_block bounded member
  have spans := fragment_emission_span member
  have run := (Fragment.emission_run member).2
  rw [instruction] at run
  exact effect_operand_interval_of_emission site (cfg_context_blocks module context impl)
    (lowerContextAt_operand_bounds module context impl).2 (initial.trans spans.1) live row run
    (spans.2.trans retained)

theorem canonical_slotInit_source_interval {fragment : Fragment} {before : LS} {emission : Emission}
    {slot source : Nat} {sourceOrigin : Option OriginId} (bounded : LiveBound before)
    (member : emission ∈ fragment.emissions (lowerEnv module impl.vars impl.results.toList) before)
    (instruction : emission.instruction = .eff (.slotInit slot source sourceOrigin))
    (initial : site.source.site.source.site.cleared.Ext before)
    (retained : (fragment.finish (lowerEnv module impl.vars impl.results.toList) before).Ext
      site.source.site.source.site.captured) :
    site.source.site.source.site.cleared.vals.size ≤ source ∧
      source < site.source.site.source.site.captured.vals.size :=
  canonical_effect_operand_interval site bounded member instruction initial retained source
    (by simp [Effect.uses])

theorem canonical_store_source_interval {fragment : Fragment} {before : LS} {emission : Emission}
    {address source : Nat} {sourceOrigin : Option OriginId} (bounded : LiveBound before)
    (member : emission ∈ fragment.emissions (lowerEnv module impl.vars impl.results.toList) before)
    (instruction : emission.instruction = .eff (.store address source sourceOrigin))
    (initial : site.source.site.source.site.cleared.Ext before)
    (retained : (fragment.finish (lowerEnv module impl.vars impl.results.toList) before).Ext
      site.source.site.source.site.captured) :
    site.source.site.source.site.cleared.vals.size ≤ source ∧
      source < site.source.site.source.site.captured.vals.size :=
  canonical_effect_operand_interval site bounded member instruction initial retained source
    (by simp [Effect.uses])

theorem canonical_call_result_interval {fragment : Fragment} {before : LS} {emission : Emission}
    {value function : Nat} {arguments : List ValueId} {callOrigin : Option OriginId}
    (bounded : LiveBound before)
    (member : emission ∈ fragment.emissions (lowerEnv module impl.vars impl.results.toList) before)
    (instruction : emission.instruction = .def value (.call function arguments callOrigin))
    (initial : site.source.site.source.site.cleared.Ext before)
    (retained : (fragment.finish (lowerEnv module impl.vars impl.results.toList) before).Ext
      site.source.site.source.site.captured) :
    site.source.site.source.site.cleared.vals.size ≤ value ∧
      value < site.source.site.source.site.captured.vals.size := by
  obtain ⟨index,body,live,row⟩ := emission_current_block bounded member
  have spans := fragment_emission_span member
  have run := (Fragment.emission_run member).2
  rw [instruction] at run
  exact context_call_result_interval site (initial.trans spans.1) live row run (spans.2.trans retained)

end Context

#print axioms emission_current_block
#print axioms canonical_slotInit_source_interval
#print axioms canonical_store_source_interval
#print axioms canonical_call_result_interval

end Goose.Lower.Validation.SourceReplacementLexicalWriters
