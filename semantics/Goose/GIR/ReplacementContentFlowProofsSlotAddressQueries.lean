import Goose.GIR.ReplacementContentFlowProofsConstantDefinitions
import Goose.GIR.ReplacementContentFlowProofsCanonicalQueries

namespace Goose.GIR

open Goose.Core ReplacementContentFlow.Model

theorem ReplacementContentFlow.forFunction_slotAddr_dependencies {module : Module}
    {func : Func} {types : Array (Option VTy)} {value : ValueId} {slot : SlotId} {block : Block}
    {returned : List RootRef}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (blockMember : block ∈ func.blocks.toList) (defined : Inst.def value (.slotAddr slot) ∈ block.insts)
    (valueKnown : ((replacementContentFlow module).forFunction func types).value value = some returned) :
    ∃ dependencies, ((replacementContentFlow module).forFunction func types).ownerDependencies value = some dependencies ∧
      dependencies ⊆ [.local slot] := by
  obtain ⟨dependencies,dependenciesAt,_⟩ := ReplacementFunctionFlow.ownerDependencies_of_value valueKnown
  refine ⟨dependencies,dependenciesAt,?_⟩
  rw [ReplacementFunctionFlow.value_model] at valueKnown
  rw [ReplacementFunctionFlow.ownerDependencies_model] at dependenciesAt
  cases stateAt : ((replacementContentFlow module).forFunction func types).model with
  | none => simp [stateAt] at valueKnown
  | some state =>
      simp only [stateAt,Option.bind_some] at valueKnown dependenciesAt
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
            have produced : ∀ current : State,
                (result func (func.valueTypes module) current value (.slotAddr slot)).AtomsWithin
                  (OwnerDependencyAtom module func [.local slot]) := by
              intro current
              unfold ReplacementContentFlow.Model.result
              split
              · simp [Roots.AtomsWithin]
              · intro atom member
                have same : atom = .local slot := List.mem_singleton.mp member
                subst atom
                exact ⟨[.local slot],ownerDependencies_local module func slot,by intro root member; exact member⟩
            have actual := reachable.result_value (.refl state) unique bounded blockMember defined
              (by intro fn args origin same; cases same) produced
            exact ownerDependencies_within_of_atomsWithin actual dependenciesAt
      · simp at localClosure

#print axioms ReplacementContentFlow.forFunction_slotAddr_dependencies

end Goose.GIR
