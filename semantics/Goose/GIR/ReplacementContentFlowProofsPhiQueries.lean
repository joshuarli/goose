import Goose.GIR.ReplacementContentFlowProofsPhi
import Goose.GIR.ReplacementContentFlowProofsCanonicalQueries

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem known_root_queries_mem {query : ValueId → Option (List RootRef)}
    {values : List ValueId} {rows : List (List RootRef)}
    (known : values.mapM query = some rows) {value : ValueId} (member : value ∈ values) :
    ∃ roots, query value = some roots ∧ roots ⊆ rows.flatten := by
  induction values generalizing rows with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mapM_cons] at known
      cases firstAt : query first with
      | none => simp [firstAt] at known
      | some firstRoots =>
          cases restAt : rest.mapM query with
          | none => simp [firstAt,restAt] at known
          | some restRoots =>
              simp [firstAt,restAt] at known
              subst rows
              rcases List.mem_cons.mp member with same | later
              · subst value
                exact ⟨firstRoots,firstAt,by intro root included; simp [included]⟩
              · obtain ⟨roots,queryAt,subset⟩ := ih restAt later
                exact ⟨roots,queryAt,by intro root included; simp [subset included]⟩

end Goose.GIR.ReplacementContentFlow.Model

namespace Goose.GIR

open Goose.Core ReplacementContentFlow.Model

theorem ReplacementContentFlow.forFunction_phi_dependencies {module : Module}
    {func : Func} {types : Array (Option VTy)} {target value : Nat} {block : Block}
    {returned : List RootRef} {inputs : List (List RootRef)}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (targetAt : func.blocks[target]? = some block) (parameter : value ∈ block.params.map Prod.fst)
    (nonentry : target ≠ 0)
    (incomingKnown : (allIncomingValues func value).mapM
      (((replacementContentFlow module).forFunction func types).ownerDependencies) = some inputs)
    (valueKnown : ((replacementContentFlow module).forFunction func types).value value = some returned) :
    ∃ dependencies, ((replacementContentFlow module).forFunction func types).ownerDependencies value = some dependencies ∧
      dependencies ⊆ inputs.flatten := by
  obtain ⟨dependencies,dependenciesAt,_⟩ := ReplacementFunctionFlow.ownerDependencies_of_value valueKnown
  refine ⟨dependencies,dependenciesAt,?_⟩
  have knownInputs : ∀ source ∈ allIncomingValues func value,
      ∃ roots, ((replacementContentFlow module).forFunction func types).ownerDependencies source = some roots ∧
        roots ⊆ inputs.flatten := fun source member => known_root_queries_mem incomingKnown member
  rw [ReplacementFunctionFlow.value_model] at valueKnown
  rw [ReplacementFunctionFlow.ownerDependencies_model] at dependenciesAt
  cases stateAt : ((replacementContentFlow module).forFunction func types).model with
  | none => simp [stateAt] at valueKnown
  | some state =>
      simp only [stateAt,Option.bind_some] at valueKnown dependenciesAt
      have actualInputs : ∀ source ∈ allIncomingValues func value,
          (flowAt state.values source).AtomsWithin (OwnerDependencyAtom module func inputs.flatten) := by
        intro source member
        obtain ⟨roots,queryAt,subset⟩ := knownInputs source member
        rw [ReplacementFunctionFlow.ownerDependencies_model] at queryAt
        simp only [stateAt,Option.bind_some] at queryAt
        exact (ownerDependencies_atomsWithin queryAt).mono (fun atom observed => observed.mono subset)
      have localClosure := stateAt
      rw [ReplacementContentFlow.forFunction_model] at localClosure
      split at localClosure
      · cases statesAt : (replacementContentFlow module).model with
        | none => simp [statesAt] at localClosure
        | some states =>
            simp only [statesAt,Option.bind_some] at localClosure
            have reachable := closeFunctionFrom_reachable localClosure
            have shape := reachable.extends.shape (start_shape func (func.valueTypes module))
            have bounded : value < func.numValues := by
              rw [← shape.values]
              exact normalize_flowAt_bounded valueKnown
            have actual := reachable.phi_value (.refl state) unique bounded targetAt parameter nonentry actualInputs
            exact ownerDependencies_within_of_atomsWithin actual dependenciesAt
      · simp at localClosure

#print axioms ReplacementContentFlow.forFunction_phi_dependencies

end Goose.GIR
