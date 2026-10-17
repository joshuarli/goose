import Goose.GIR.ReplacementContentFlowProofsScopedOrigins
import Goose.GIR.ReplacementContentFlowProofsPhiQueries

namespace Goose.GIR

open Goose.Core ReplacementContentFlow.Model

theorem ReplacementContentFlow.forFunction_scoped_dependencies {module : Module}
    {func : Func} {types : Array (Option VTy)} {selected : ValueId → Prop} {leaves : List ValueId}
    {value : ValueId} {returned : List RootRef} {inputs : List (List RootRef)}
    (bounded : ∀ value, selected value → value < func.numValues)
    (separate : ∀ entry, func.blocks[0]? = some entry →
      ∀ value, selected value → value ∉ leaves → value ∉ entry.params.map Prod.fst)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
      selected value → value ∈ leaves ∨ ∃ source, selected source ∧
        (∀ fn args origin, op ≠ .call fn args origin) ∧
        ∀ state, result func (func.valueTypes module) state value op = flowAt state.values source)
    (incoming : ∀ value, selected value → value ∉ leaves →
      ∀ source ∈ allIncomingValues func value, selected source)
    (leavesKnown : leaves.mapM (((replacementContentFlow module).forFunction func types).ownerDependencies) = some inputs)
    (chosen : selected value)
    (valueKnown : ((replacementContentFlow module).forFunction func types).value value = some returned) :
    ∃ dependencies, ((replacementContentFlow module).forFunction func types).ownerDependencies value = some dependencies ∧
      dependencies ⊆ inputs.flatten := by
  obtain ⟨dependencies,dependenciesAt,_⟩ := ReplacementFunctionFlow.ownerDependencies_of_value valueKnown
  refine ⟨dependencies,dependenciesAt,?_⟩
  have knownInputs : ∀ source ∈ leaves,
      ∃ roots, ((replacementContentFlow module).forFunction func types).ownerDependencies source = some roots ∧
        roots ⊆ inputs.flatten := fun source member => known_root_queries_mem leavesKnown member
  rw [ReplacementFunctionFlow.value_model] at valueKnown
  rw [ReplacementFunctionFlow.ownerDependencies_model] at dependenciesAt
  cases stateAt : ((replacementContentFlow module).forFunction func types).model with
  | none => simp [stateAt] at valueKnown
  | some state =>
      simp only [stateAt,Option.bind_some] at valueKnown dependenciesAt
      have observed : ∀ source ∈ leaves,
          (flowAt state.values source).AtomsWithin (OwnerDependencyAtom module func inputs.flatten) := by
        intro source member
        obtain ⟨roots,queryAt,subset⟩ := knownInputs source member
        rw [ReplacementFunctionFlow.ownerDependencies_model] at queryAt
        simp only [stateAt,Option.bind_some] at queryAt
        exact (ownerDependencies_atomsWithin queryAt).mono (fun atom dependency => dependency.mono subset)
      have localClosure := stateAt
      rw [ReplacementContentFlow.forFunction_model] at localClosure
      split at localClosure
      · cases statesAt : (replacementContentFlow module).model with
        | none => simp [statesAt] at localClosure
        | some states =>
            simp only [statesAt,Option.bind_some] at localClosure
            have reachable := closeFunctionFrom_reachable localClosure
            have actual := reachable.scoped_values (.refl state) bounded separate definitions incoming observed
            exact ownerDependencies_within_of_atomsWithin (actual value chosen) dependenciesAt
      · simp at localClosure

#print axioms ReplacementContentFlow.forFunction_scoped_dependencies

end Goose.GIR
