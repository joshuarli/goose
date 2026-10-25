import Goose.Lower.Validation.SourceOccurrenceInstructions

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

private theorem native_site {env : PEnv} {root : DemandNode} {le : LEnv}
    {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    (sites : OccurrenceSitesBuilder env root [] le state func types upper)
    (blocks : func.blocks = finishBlocks state.blocks)
    {index position owner value : Nat} {origin : OriginId} {block : GIR.Block}
    (blockAt : func.blocks[index]? = some block)
    (instructionAt : block.insts[position]? = some (.eff (.replace owner value (some origin)))) :
    Nonempty (SiteOccurrences env root [] le state func types upper index position owner value origin) := by
  rw [blocks, finishBlocks, Array.getElem?_map] at blockAt
  cases bodyAt : state.blocks[index]? with
  | none => simp [bodyAt] at blockAt
  | some body =>
    have same : (⟨body.params, body.insts.toList⟩ : GIR.Block) = block := by
      simpa only [bodyAt, Option.map_some, Option.some.injEq] using blockAt
    subst block
    exact sites index body bodyAt position _ (by simpa using instructionAt)

theorem accepted_context_replacement_occurrences {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    {index position owner value : Nat} {origin : OriginId} {block : GIR.Block}
    (blockAt : (lowerContextAt module ctx impl).blocks[index]? = some block)
    (instructionAt : block.insts[position]? = some (.eff (.replace owner value (some origin)))) :
    ∃ upper, ProvenanceBelow
      ((lowerContextAt module ctx impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module ctx impl).valueTypes (lower module)) (lower module).rootCount) upper ∧
      Nonempty (SiteOccurrences ⟨module, impl, ctx, []⟩ (.block impl.body) []
        (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
        (lowerContextAt module ctx impl) ((lowerContextAt module ctx impl).valueTypes (lower module))
        upper index position owner value origin) := by
  obtain ⟨roots, range, after, upper, replayed, ready, returned, retained, ledger, sites⟩ :=
    accepted_context_occurrence_replay_canonical accepted contextRow implementationRow
  have below := ready.finished_provenance (cfg_context_blocks module ctx impl)
    (accepted_context_provenance_seed accepted contextRow implementationRow ready.slotsEq ready.recipes retained)
    (lower module).rootCount
  refine ⟨upper, ?_, native_site sites (cfg_context_blocks module ctx impl) blockAt instructionAt⟩
  simpa only [module_implTypes_eq_native] using below

theorem accepted_global_replacement_occurrences {module : Core.Module} {global : Core.Global}
    {index : GlobalId} (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global)
    {blockIndex position owner value : Nat} {origin : OriginId} {block : GIR.Block}
    (blockAt : (lowerGlobal module global).init.blocks[blockIndex]? = some block)
    (instructionAt : block.insts[position]? = some (.eff (.replace owner value (some origin)))) :
    ∃ upper, ProvenanceBelow
      ((lowerGlobal module global).init.provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount) upper ∧
      Nonempty (SiteOccurrences ⟨module, Core.initImpl, Core.initContext, []⟩ (.expression global.init) []
        (lowerEnv module #[] [global.ty]) (cfg_globalState module global)
        (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
        upper blockIndex position owner value origin) := by
  obtain ⟨roots, after, upper, replayed, ready, returned, ledger, sites⟩ :=
    accepted_global_occurrence_replay_canonical accepted globalRow
  have below := ready.finished_provenance (cfg_global_blocks module global)
    (global_provenance_seed module global _ upper ready.recipes) (lower module).rootCount
  refine ⟨upper, ?_, native_site sites (cfg_global_blocks module global) blockAt instructionAt⟩
  simpa only [module_implTypes_eq_native] using below

#print axioms accepted_context_replacement_occurrences
#print axioms accepted_global_replacement_occurrences

end Goose.Lower.Validation.ReplacementContentFlowSource
