import Goose.GIR.ReplacementContentFlowProofsScopedContent
import Goose.Lower.Validation.ReplacementOwnerDependencyApart

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR ReplacementContentFlow.Model

theorem forFunction_scoped_content_atoms {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {selected slots contents : Nat → Prop} {leaves : List ValueId}
    {queries : ReplacementQueries} {owner : ValueId} {final : State}
    (bounded : ∀ value, selected value → value < func.numValues)
    (separate : ∀ entry, func.blocks[0]? = some entry →
      ∀ value, selected value → value ∉ leaves → value ∉ entry.params.map Prod.fst)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
      selected value → value ∈ leaves ∨
        (∃ function arguments origin, op = .call function arguments origin) ∨
        ∃ source, selected source ∧ (∀ function arguments origin, op ≠ .call function arguments origin) ∧
          ∀ state, result func (func.valueTypes module) state value op = flowAt state.values source)
    (incoming : ∀ value, selected value → value ∉ leaves →
      ∀ source ∈ allIncomingValues func value, selected source)
    (leafQueries : ∀ value ∈ leaves, ∃ roots,
      ((replacementContentFlow module).forFunction func types).ownerDependencies value = some roots ∧
        ReplacementApart queries owner (some roots))
    (initial : (start func (func.valueTypes module)).ScopedMemoryWithin slots contents
      (OwnerDependencyApart module func queries owner))
    (calls : ∀ states, (replacementContentFlow module).model = some states →
      ∀ final, ((replacementContentFlow module).forFunction func types).model = some final →
      ∀ block ∈ func.blocks.toList, ∀ value function arguments origin,
      Inst.def value (.call function arguments origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin selected slots contents (OwnerDependencyApart module func queries owner) →
        current.Extends final →
        (selected value → value ∉ leaves →
          ((callState module states func current function arguments).1).AtomsWithin
            (OwnerDependencyApart module func queries owner)) ∧
        ((callState module states func current function arguments).2).ScopedMemoryWithin slots contents
          (OwnerDependencyApart module func queries owner))
    (initializations : ∀ final, ((replacementContentFlow module).forFunction func types).model = some final →
      ∀ block ∈ func.blocks.toList, ∀ slot value origin, Inst.eff (.slotInit slot value origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin selected slots contents (OwnerDependencyApart module func queries owner) →
        current.Extends final → slots slot → (flowAt current.values value).AtomsWithin
          (OwnerDependencyApart module func queries owner))
    (stores : ∀ final, ((replacementContentFlow module).forFunction func types).model = some final →
      ∀ block ∈ func.blocks.toList, ∀ address value origin, Inst.eff (.store address value origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin selected slots contents (OwnerDependencyApart module func queries owner) →
        current.Extends final → valRefLike (func.valueTypes module) value = true →
        (write func (touchValues (func.valueTypes module) current [address]) (flowAt current.values address)
          (flowAt current.values value)).ScopedMemoryWithin slots contents (OwnerDependencyApart module func queries owner))
    (finalAt : ((replacementContentFlow module).forFunction func types).model = some final) :
    final.ScopedContentWithin selected slots contents (OwnerDependencyApart module func queries owner) := by
  have observed : ∀ value ∈ leaves,
      (flowAt final.values value).AtomsWithin (OwnerDependencyApart module func queries owner) := by
    intro value member
    obtain ⟨roots, rootsAt, apart⟩ := leafQueries value member
    rw [ReplacementFunctionFlow.ownerDependencies_model, finalAt] at rootsAt
    simp only [Option.bind_some] at rootsAt
    exact ownerDependencies_atoms_apart rootsAt apart
  have closure := finalAt
  rw [ReplacementContentFlow.forFunction_model] at closure
  split at closure
  · cases statesAt : (replacementContentFlow module).model with
    | none => simp [statesAt] at closure
    | some states =>
      simp only [statesAt, Option.bind_some] at closure
      exact (closeFunctionFrom_reachable closure).scoped_content (.refl final) initial bounded separate definitions incoming
        (calls states statesAt final finalAt) (initializations final finalAt) (stores final finalAt) observed
  · simp at closure

#print axioms forFunction_scoped_content_atoms

end Goose.Lower.Validation
