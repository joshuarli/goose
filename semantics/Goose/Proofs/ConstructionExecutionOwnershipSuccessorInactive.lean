import Goose.Proofs.ConstructionExecutionOwnershipInactivePrimitives
import Goose.Proofs.ConstructionExecutionOwnershipSuccessorKernel

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

def DestinationSuccessorKeysInactive (state : ConstructionState) : Prop :=
  ∀ (key next : DestinationId), state.destinationSuccessors.lookup key = some next →
    ∃ row, state.destinations[key]? = some row ∧ activeProgress row.progress = false

theorem initial_destinationSuccessorKeysInactive : DestinationSuccessorKeysInactive .initial := by
  intro key next edge
  simp [ConstructionState.initial] at edge

theorem destinationSuccessorKeysInactive_live_terminal (state : ConstructionState)
    (valid : DestinationSuccessorKeysInactive state) (id : DestinationId) (row : PendingDestination)
    (present : state.destinations[id]? = some row) (live : activeProgress row.progress = true) :
    state.destinationSuccessors.lookup id = none := by
  cases edge : state.destinationSuccessors.lookup id with
  | none => rfl
  | some next =>
      obtain ⟨inactive, found, dead⟩ := valid id next edge
      have same : inactive = row := Option.some.inj (found.symm.trans present)
      subst inactive
      exact False.elim (Bool.noConfusion (live.symm.trans dead))

theorem destinationSuccessorKeysInactive_built_terminal (state : ConstructionState)
    (valid : DestinationSuccessorKeysInactive state) (id : DestinationId) (row : PendingDestination)
    (present : state.destinations[id]? = some row) (count : Nat) (built : row.progress = .built count) :
    state.destinationSuccessors.lookup id = none :=
  destinationSuccessorKeysInactive_live_terminal state valid id row present (by simp only [built, activeProgress])

theorem destinationSuccessorKeysInactive_extension (before after : ConstructionState)
    (successors : after.destinationSuccessors = before.destinationSuccessors)
    (inactive : InactiveBackingExtension before after) (valid : DestinationSuccessorKeysInactive before) :
    DestinationSuccessorKeysInactive after := by
  intro key next edge
  have oldEdge : before.destinationSuccessors.lookup key = some next := by simpa only [successors] using edge
  obtain ⟨oldRow, present, dead⟩ := valid key next oldEdge
  obtain ⟨row, found, stillDead, _⟩ := inactive key oldRow present dead
  exact ⟨row, found, stillDead⟩

theorem constructionPrimitive_successorKeysInactive {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (lifecycle : DestinationLifecycleInvariant state) (valid : DestinationSuccessorKeysInactive state) :
    DestinationSuccessorKeysInactive (action state).finalState :=
  destinationSuccessorKeysInactive_extension state _ (constructionPrimitive_successorMap action primitive state)
    (constructionPrimitive_inactiveBacking action primitive state lifecycle) valid

end Goose.Proofs.ConstructionExecutionOwnership
