import Goose.Lower.Validation.SummaryPreservationRefinedSummary
import Goose.Lower.Validation.SummaryPreservationEffectMonotonicity
import Goose.Lower.Validation.SummaryPreservationTransfer

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem accepted_source_effects_summaryClosed {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {source : RState} {roots : List RootRef}
    {range : Nat × Nat} {actual : Core.Eff}
    (accepted : Core.validate module = .ok ())
    (contextLookup : module.contexts[context]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl)
    (replayed : rpBlockValue ⟨module, impl, ctx, []⟩ [] impl.body ⟨impl.params.size, {}⟩ =
      .ok ((roots, range), source))
    (refined : EffectRefinement (lowerContextAt module ctx impl) actual source.eff) :
    (lowerContextAt module ctx impl).summaryClosed actual = .ok () := by
  obtain ⟨checkedImpl, lookup, checked⟩ := (validate_modOk module accepted).ctx context ctx contextLookup
  rw [implLookup] at lookup
  cases lookup
  obtain ⟨acceptedRoots, acceptedRange, acceptedState, body, _, summary⟩ := checked.body
  rw [replayed] at body
  cases body
  exact refined_checkSummary_lowerContextAt accepted contextLookup implLookup summary refined

theorem computed_effects_refine {module : GIR.Module} {func : Func}
    {results : Array (List RootRef)} {upper : Prov} {source : Core.Eff}
    (instructions : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      InstructionRootsClosed results (func.valueTypes module) func upper inst)
    (start : ProvenanceBelow (provStart (func.valueTypes module) func) upper)
    (effects : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      EffectRefinement func (func.effectStep module (func.valueTypes module) upper {} inst) source)
    (rootCount : Nat) :
    EffectRefinement func
      (func.effects module (func.provenance results (func.valueTypes module) rootCount)) source :=
  effects_refine_of_upper (provenance_below instructions start rootCount) effects

theorem accepted_computed_summaryClosed {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {source : RState} {roots : List RootRef} {range : Nat × Nat}
    {results : Array (List RootRef)} {upper : Prov}
    (accepted : Core.validate module = .ok ())
    (contextLookup : module.contexts[context]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl)
    (replayed : rpBlockValue ⟨module, impl, ctx, []⟩ [] impl.body ⟨impl.params.size, {}⟩ =
      .ok ((roots, range), source))
    (instructions : ∀ block ∈ (lowerContextAt module ctx impl).blocks.toList, ∀ inst ∈ block.insts,
      InstructionRootsClosed results ((lowerContextAt module ctx impl).valueTypes (lower module))
        (lowerContextAt module ctx impl) upper inst)
    (start : ProvenanceBelow
      (provStart ((lowerContextAt module ctx impl).valueTypes (lower module))
        (lowerContextAt module ctx impl)) upper)
    (effects : ∀ block ∈ (lowerContextAt module ctx impl).blocks.toList, ∀ inst ∈ block.insts,
      EffectRefinement (lowerContextAt module ctx impl)
        ((lowerContextAt module ctx impl).effectStep (lower module)
          ((lowerContextAt module ctx impl).valueTypes (lower module)) upper {} inst) source.eff)
    (rootCount : Nat) :
    (lowerContextAt module ctx impl).summaryClosed
      ((lowerContextAt module ctx impl).effects (lower module)
        ((lowerContextAt module ctx impl).provenance results
          ((lowerContextAt module ctx impl).valueTypes (lower module)) rootCount)) = .ok () :=
  accepted_source_effects_summaryClosed accepted contextLookup implLookup replayed
    (computed_effects_refine instructions start effects rootCount)

end Goose.Lower.Validation.SummaryPreservation
