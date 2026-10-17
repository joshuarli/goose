import Goose.Proofs.ConstructionExecutionOwnershipEvaluationContext
import Goose.Proofs.OwnershipAmbientFrontiers
import Goose.Proofs.ConstructionExecutionProtocolQueries

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct

abbrev PreservesOwnershipAmbient (shape : OwnershipResultShape α) (action : EvalM α) : Prop :=
  ∀ (state : ExecutionState) (ambient : OwnershipAmbient),
    OwnershipAmbientInvariant state.construction ambient → OwnershipAmbientOutcome ambient shape (action state)

theorem ownershipAmbientInvariant_returned (state : ConstructionState) (ambient : OwnershipAmbient)
    (carriers : List Carrier) (valid : OwnershipAmbientInvariant state ambient) :
    OwnershipAmbientInvariant state (.returned carriers :: ambient) := by
  refine ⟨valid.structural, ?_, ⟨retainedOutsideTickets_nil state _, valid.boundaries⟩⟩
  intro id row present inactive supported
  obtain ⟨retained, member, descendant⟩ := valid.anchors id row present inactive supported
  refine ⟨retained, ?_, descendant⟩
  simp only [OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers,
    completedCarrierIds_append, List.mem_append]
  exact Or.inr member

theorem ownershipAmbient_pure (shape : OwnershipResultShape α) (value : α) :
    PreservesOwnershipAmbient shape (pure value) := by
  intro state ambient valid
  exact ownershipAmbientInvariant_returned state.construction ambient _ valid

theorem ownershipAmbient_stop (shape : OwnershipResultShape α) (reason : Goose.Core.Stop) :
    PreservesOwnershipAmbient shape (EvalM.stop reason) := by
  intro state ambient valid
  exact valid.structural

theorem ownershipAmbient_stateQuery (shape : OwnershipResultShape α) (action : EvalM α)
    (query : Goose.Proofs.ConstructionExecutionProtocol.StateQuery action) :
    PreservesOwnershipAmbient shape action := by
  intro state ambient valid
  have unchanged := query state
  cases result : action state with
  | ok value after =>
      rw [result] at unchanged
      change after = state at unchanged
      subst after
      exact ownershipAmbientInvariant_returned state.construction ambient _ valid
  | stop reason after =>
      rw [result] at unchanged
      change after = state at unchanged
      subst after
      exact valid.structural
  | escape address carriers after =>
      rw [result] at unchanged
      change after = state at unchanged
      subst after
      exact ownershipAmbientInvariant_returned state.construction ambient carriers valid
  | jump target kind after =>
      rw [result] at unchanged
      change after = state at unchanged
      subst after
      cases kind with
      | breakValue carriers => exact ownershipAmbientInvariant_returned state.construction ambient carriers valid
      | continueLoop => exact valid

theorem ownershipAmbient_bind_none (action : EvalM α) (next : α → EvalM β)
    (shape : OwnershipResultShape β) (first : PreservesOwnershipAmbient .none action)
    (remaining : ∀ value, PreservesOwnershipAmbient shape (next value)) :
    PreservesOwnershipAmbient shape (action >>= next) := by
  intro state ambient valid
  have firstValid := first state ambient valid
  cases result : action state with
  | ok value after =>
      simp only [bind, result]
      simp only [result, OwnershipAmbientOutcome, OwnershipResultShape.retainedCarriers] at firstValid
      exact remaining value after ambient
        ((ownershipAmbientInvariant_returned_nil after.construction ambient).mp firstValid)
  | stop reason after => simpa only [bind, result, OwnershipAmbientOutcome] using firstValid
  | escape address carriers after => simpa only [bind, result, OwnershipAmbientOutcome] using firstValid
  | jump target kind after =>
      cases kind <;> simpa only [bind, result, OwnershipAmbientOutcome] using firstValid

end Goose.Proofs.ConstructionExecutionOwnership
