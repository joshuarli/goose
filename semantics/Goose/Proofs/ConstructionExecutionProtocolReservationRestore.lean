import Goose.Proofs.ConstructionExecutionProtocolReservations
import Goose.Proofs.ConstructionExecutionProtocolDestination

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

theorem destinationLifecycleInvariant_restore_snapshot (state : ConstructionState)
    (snapshot current : PendingDestination) (count : Nat) (selected : DestinationId)
    (present : state.destinations[snapshot.capability.id]? = some current)
    (exiting : current.progress = .exiting count selected)
    (bounds : SavedDestinationBounds state snapshot.capability.id snapshot)
    (phaseValid : ReservedSnapshotPhase state snapshot)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with
      destinations := state.destinations.set! snapshot.capability.id snapshot } := by
  refine ⟨?_, destinationCapabilities_replace state snapshot.capability.id snapshot rfl valid.2.1,
    ?_, ?_⟩
  · intro index
    change match (state.destinations.set! snapshot.capability.id snapshot)[index]? with
      | none => runDestinationTrace index .unseen state.events = some .unseen
      | some destination => ∃ phase,
          runDestinationTrace index .unseen state.events = some phase ∧
          phase.matchesDestination destination
    by_cases same : snapshot.capability.id = index
    · subst index
      simp only [Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_self_of_lt bounds.allocated]
      have previous := valid.1 snapshot.capability.id
      rw [present] at previous
      obtain ⟨phase, accepted, _⟩ := previous
      have compatible := phaseValid current present
      simp only [exiting] at compatible
      exact ⟨phase, accepted, compatible phase accepted⟩
    · cases observed : state.destinations[index]? <;>
        simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same, observed] using valid.1 index
  · exact destinationStorageReferences_replace state snapshot.capability.id snapshot state.storage
      (Nat.le_refl _) bounds.writeStorage bounds.receivingStorage valid.2.2.1
  · intro index destination found
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at found
    by_cases same : snapshot.capability.id = index
    · subst index
      simp only [bounds.allocated, ↓reduceIte, Option.some.injEq] at found
      subst destination
      exact bounds.owner
    · exact valid.2.2.2 index destination (by simpa only [same, ↓reduceIte] using found)

end Goose.Proofs.ConstructionExecutionProtocol
