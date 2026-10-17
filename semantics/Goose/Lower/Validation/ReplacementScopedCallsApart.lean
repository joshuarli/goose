import Goose.GIR.ReplacementContentFlowProofsScopedCalls
import Goose.Lower.Validation.ReplacementOwnerDependencyApart

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR ReplacementContentFlow.Model

theorem forFunction_scoped_calls_apart {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {selected : ValueId → Prop} {leaves : List ValueId}
    {queries : ReplacementQueries} {owner value : ValueId} {returned : List RootRef}
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
    (calls : ∀ states, (replacementContentFlow module).model = some states →
      ∀ final, ((replacementContentFlow module).forFunction func types).model = some final →
      ∀ block ∈ func.blocks.toList, ∀ value function arguments origin,
      Inst.def value (.call function arguments origin) ∈ block.insts → selected value → value ∉ leaves →
      ∀ current, current.ScopedValuesWithin selected (OwnerDependencyApart module func queries owner) →
        current.Extends final →
        ((callState module states func current function arguments).1).AtomsWithin
          (OwnerDependencyApart module func queries owner))
    (chosen : selected value)
    (known : ((replacementContentFlow module).forFunction func types).value value = some returned) :
    ∃ roots, ((replacementContentFlow module).forFunction func types).ownerDependencies value = some roots ∧
      ReplacementApart queries owner (some roots) := by
  obtain ⟨roots, queryAt, _⟩ := ReplacementFunctionFlow.ownerDependencies_of_value known
  refine ⟨roots, queryAt, ?_⟩
  rw [ReplacementFunctionFlow.value_model] at known
  rw [ReplacementFunctionFlow.ownerDependencies_model] at queryAt
  cases finalAt : ((replacementContentFlow module).forFunction func types).model with
  | none => simp [finalAt] at known
  | some final =>
    simp only [finalAt, Option.bind_some] at known queryAt
    have observed : ∀ value ∈ leaves,
        (flowAt final.values value).AtomsWithin (OwnerDependencyApart module func queries owner) := by
      intro value member
      obtain ⟨roots, rootAt, apart⟩ := leafQueries value member
      rw [ReplacementFunctionFlow.ownerDependencies_model] at rootAt
      simp only [finalAt, Option.bind_some] at rootAt
      exact ownerDependencies_atoms_apart rootAt apart
    have closure := finalAt
    rw [ReplacementContentFlow.forFunction_model] at closure
    split at closure
    · cases statesAt : (replacementContentFlow module).model with
      | none => simp [statesAt] at closure
      | some states =>
        simp only [statesAt, Option.bind_some] at closure
        have reachable := closeFunctionFrom_reachable closure
        have actual := reachable.scoped_call_values (.refl final) bounded separate definitions incoming
          (calls states statesAt final finalAt) observed
        exact ownerDependencies_apart_of_atoms (actual value chosen) queryAt
    · simp at closure

#print axioms forFunction_scoped_calls_apart

end Goose.Lower.Validation
