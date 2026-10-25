import Goose.Lower.Validation.ReplacementSourceSafety

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ReplacementSiteAt.checkReplace_at_prefix {le : LEnv} {state : LS}
    {index position owner value : Nat} {origin : OriginId}
    (witness : ReplacementSiteAt le state index position owner value origin)
    {module : GIR.Module} {func : Func}
    (builder : EmittedBuilder le initState state)
    (blocks : func.blocks = finishBlocks state.blocks) (slots : func.slots = le.slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = le.globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = le.sigs)
    (structs : module.structs = le.mod.structs) (profile : module.profile = le.mod.profile)
    (graphs : MutableSnapshotGraphs module func state)
    (closed : ∀ body ∈ state.blocks.toList, ClosedBlock body)
    {queries : ReplacementQueries}
    (emitted : EmitsOnly (ReplacementInstApart module (func.valueTypes module) queries owner)
      witness.source.site.cleared witness.source.site.captured)
    {body : GIR.Block} (row : func.blocks[index]? = some body)
    {head tail : List Inst}
    (split : body.insts = head ++ .eff (.replace owner value (some origin)) :: tail)
    (positionAt : head.length = position) (label : String) :
    checkReplace module func (func.valueTypes module) queries (freshRuns func (func.valueTypes module)) label
      (head.foldl (transferEmptyInst module (func.valueTypes module) queries)
        (ReplacementRegionFacts witness.source.site.cleared witness.source.site.captured owner index))
      (.eff (.replace owner value (some origin))) = .ok () := by
  obtain ⟨ownerType, fresh⟩ := witness.source.owner_fresh builder blocks slots globals sigs structs profile graphs closed
  have cleared := witness.prefix_cleared emitted blocks row split positionAt
  apply checkReplace_of_safe
  intro actualOwner actualValue actualOrigin same
  cases same
  exact ⟨ownerType, fresh, cleared⟩

#print axioms ReplacementSiteAt.checkReplace_at_prefix

end Goose.Lower.Validation
