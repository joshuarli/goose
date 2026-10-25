import Goose.Lower.Validation.SummaryPreservationComputedSummary
import Goose.Lower.Validation.SummaryPreservationReturnLedger

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem finishBlocks_instruction_member {state : LS} {block : GIR.Block} {inst : Inst}
    (blockMember : block ∈ (finishBlocks state.blocks).toList) (instMember : inst ∈ block.insts) :
    inst ∈ state.insts := by
  have mapped : block ∈ state.blocks.toList.map (fun builder =>
      ({ params := builder.params, insts := builder.insts.toList } : GIR.Block)) := by
    simpa only [finishBlocks, Array.toList_map] using blockMember
  obtain ⟨builder, builderMember, rfl⟩ := List.mem_map.mp mapped
  exact List.mem_flatMap.mpr ⟨builder, builderMember, instMember⟩

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {state : LS} {upper : Prov}

theorem finished_instructions
    (ready : ReplayBuilder module results vt func target le scopeCount slots state upper)
    (blocks : func.blocks = finishBlocks state.blocks) :
    ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      InstructionRootsClosed results vt func upper inst := by
  intro block blockMember inst instMember
  have member := finishBlocks_instruction_member (state := state) (blocks ▸ blockMember) instMember
  have closed := ready.roots.instructions inst member
  have same : { func with blocks := finishBlocks state.blocks } = func := by rw [← blocks]
  simpa only [same] using closed

theorem finished_effects
    (ready : ReplayBuilder module results vt func target le scopeCount slots state upper)
    (blocks : func.blocks = finishBlocks state.blocks) :
    ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      EffectRefinement func (func.effectStep module vt upper {} inst) target := by
  intro block blockMember inst instMember
  exact ready.effects inst (finishBlocks_instruction_member (state := state) (blocks ▸ blockMember) instMember)

theorem finished_provenance
    (ready : ReplayBuilder module results vt func target le scopeCount slots state upper)
    (blocks : func.blocks = finishBlocks state.blocks)
    (start : ProvenanceBelow (provStart vt func) upper) (rootCount : Nat) :
    ProvenanceBelow (func.provenance results vt rootCount) upper :=
  provenance_below (ready.finished_instructions blocks) start rootCount

theorem finished_returnedRoots {declared : List RootRef}
    (ready : ReplayBuilder module results vt func target le scopeCount slots state upper)
    (blocks : func.blocks = finishBlocks state.blocks)
    (start : ProvenanceBelow (provStart vt func) upper)
    (returns : BuilderReturnsBound upper declared state) (rootCount : Nat) :
    ∀ root ∈ func.returnedRoots (func.provenance results vt rootCount), root ∈ declared := by
  have bounded := ready.finished_provenance blocks start rootCount
  have returned := returnedRoots_finishBlocks_below (func := func) bounded returns
  have same : { func with blocks := finishBlocks state.blocks } = func := by rw [← blocks]
  simpa only [same] using returned

theorem finished_computed_effects
    (ready : ReplayBuilder module results vt func target le scopeCount slots state upper)
    (blocks : func.blocks = finishBlocks state.blocks)
    (types : vt = func.valueTypes module)
    (start : ProvenanceBelow (provStart vt func) upper) (rootCount : Nat) :
    EffectRefinement func (func.effects module (func.provenance results vt rootCount)) target := by
  subst vt
  exact computed_effects_refine (ready.finished_instructions blocks) start (ready.finished_effects blocks) rootCount

end ReplayBuilder

theorem accepted_finished_summaryClosed {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {source : RState} {roots : List RootRef} {range : Nat × Nat}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {le : LEnv} {scopeCount : Nat}
    {slots : Array (List RootRef)} {state : LS} {upper : Prov}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (replayed : rpBlockValue ⟨module, impl, ctx, []⟩ [] impl.body ⟨impl.params.size, {}⟩ =
      .ok ((roots, range), source))
    (ready : ReplayBuilder (lower module) results vt (lowerContextAt module ctx impl) source.eff
      le scopeCount slots state upper)
    (blocks : (lowerContextAt module ctx impl).blocks = finishBlocks state.blocks)
    (types : vt = (lowerContextAt module ctx impl).valueTypes (lower module))
    (start : ProvenanceBelow (provStart vt (lowerContextAt module ctx impl)) upper)
    (rootCount : Nat) :
    (lowerContextAt module ctx impl).summaryClosed
      ((lowerContextAt module ctx impl).effects (lower module)
        ((lowerContextAt module ctx impl).provenance results vt rootCount)) = .ok () :=
  accepted_source_effects_summaryClosed accepted contextRow implementationRow replayed
    (ready.finished_computed_effects blocks types start rootCount)

#print axioms ReplayBuilder.finished_provenance
#print axioms ReplayBuilder.finished_returnedRoots
#print axioms ReplayBuilder.finished_computed_effects
#print axioms accepted_finished_summaryClosed

end Goose.Lower.Validation.SummaryPreservation
