import Goose.Lower.Validation.ReplacementSourceRequirements
import Goose.Lower.Validation.ReplacementRequirements

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem checkShrinkReplace_of_source_sites {le : LEnv} {state : LS}
    {module : GIR.Module} {func : Func}
    (builder : EmittedBuilder le initState state)
    (blocks : func.blocks = finishBlocks state.blocks) (slots : func.slots = le.slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = le.globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = le.sigs)
    (structs : module.structs = le.mod.structs) (profile : module.profile = le.mod.profile)
    (graphs : MutableSnapshotGraphs module func state)
    (closed : ∀ body ∈ state.blocks.toList, ClosedBlock body)
    (nonempty : 0 < func.blocks.size)
    (known : ∀ index, index < func.blocks.size →
      EmptyStateKnown (emptyFactsAtBlocks module func (func.valueTypes module)
        (replacementQueries module func (func.valueTypes module))) index)
    (sites : ∀ (index : BlockId) (body : BlockB), state.blocks[index]? = some body →
      ∀ (position owner value : Nat) (origin : Option OriginId),
        body.insts[position]? = some (.eff (.replace owner value origin)) →
        ∃ sourceOrigin, origin = some sourceOrigin ∧
          ∃ witness : ReplacementSiteAt le state index position owner value sourceOrigin,
            EmitsOnly (ReplacementInstApart module (func.valueTypes module)
              (replacementQueries module func (func.valueTypes module)) owner)
              witness.source.site.cleared witness.source.site.captured)
    (label : String) : checkShrinkReplace module label func (func.valueTypes module) = .ok () := by
  let queries := replacementQueries module func (func.valueTypes module)
  let required := replacementSourceRequirements le state module (func.valueTypes module) queries
  have factClosure : EmptyFactsClosed module func (func.valueTypes module) queries required :=
    replacementSourceRequirements_closed closed blocks
  have entry : required 0 = [] := replacementSourceRequirements_entry _ _ _ _ _
  have retained := emptyFactsAtBlocks_required module func (func.valueTypes module) queries required
    factClosure entry nonempty
  apply checkShrinkReplace_of_blocks
  intro index body row
  obtain ⟨facts, factsAt⟩ := known index (Array.getElem?_eq_some_iff.mp row).1
  refine ⟨facts, factsAt, ?_⟩
  apply ReplacementTrace.mono (subset := retained index facts factsAt)
  apply replacementTrace_of_prefixes
  intro head instruction tail separated owner value origin matched
  subst instruction
  obtain ⟨raw, rawAt, rawBody⟩ := finishBlocks_row_source blocks row
  have rawSplit : raw.insts.toList = head ++ .eff (.replace owner value origin) :: tail := by
    simpa only [← rawBody, cfgBlock] using separated
  have selected : raw.insts[head.length]? = some (.eff (.replace owner value origin)) := by
    rw [← Array.getElem?_toList, rawSplit]
    simp
  obtain ⟨sourceOrigin, sourceEq, witness, apart⟩ := sites index raw rawAt head.length owner value origin selected
  subst origin
  obtain ⟨ownerType, fresh⟩ := witness.source.owner_fresh builder blocks slots globals sigs structs profile graphs closed
  have bound := witness.source.owner_bound builder blocks slots globals sigs structs profile graphs closed
  exact ⟨ownerType, fresh, witness.source_prefix_cleared apart bound blocks row separated rfl⟩

#print axioms checkShrinkReplace_of_source_sites

end Goose.Lower.Validation
