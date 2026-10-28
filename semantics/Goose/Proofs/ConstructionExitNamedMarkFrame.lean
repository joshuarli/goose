import Goose.Proofs.ConstructionExitNamedMarkLineage
import Goose.Proofs.ConstructionExecutionProtocolNamedReservationMark

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem mark_named_exact_update (state after : ConstructionState) (token incoming selected : Nat)
    (snapshot : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active (.named .awaitingSource) incoming selected snapshot))
    (marked : markNamedReservation token state = .ok () after) :
    ∃ next, after = { state with exitReservations := state.exitReservations.set! token (.active (.named .ready) incoming selected next) } := by
  simp only [markNamedReservation, ConstructionM.get, ticket, bind, pure, lookupDestination_result] at marked
  cases present : state.destinations[selected]? with
  | none => simp [present, ConstructionM.fail] at marked
  | some row =>
    simp only [present] at marked
    cases progress : row.progress <;> simp only [progress] at marked <;> try (simp [ConstructionM.fail] at marked)
    all_goals
      simp only [pure, lookupStorage_result, bind] at marked
      cases stored : state.storage[row.storage]? with
      | none => simp [stored, ConstructionM.fail] at marked
      | some storage =>
        simp only [stored] at marked
        split at marked
        · simp [ConstructionM.fail] at marked
        · simp only [ConstructionM.get, ConstructionM.set, bind, pure, ConstructionResult.ok.injEq, true_and] at marked
          subst after
          exact ⟨_, rfl⟩

theorem mark_named_lifecycle_and_frame (state after : ConstructionState) (token incoming selected : Nat)
    (snapshot : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active (.named .awaitingSource) incoming selected snapshot))
    (lifecycle : ReservationLifecycleInvariant state)
    (marked : markNamedReservation token state = .ok () after) :
    ReservationLifecycleInvariant after ∧
    ∃ next, after = { state with exitReservations := state.exitReservations.set! token (.active (.named .ready) incoming selected next) } := by
  have retained := markNamedReservation_lifecycle token state lifecycle
  rw [marked] at retained
  exact ⟨retained, mark_named_exact_update state after token incoming selected snapshot ticket marked⟩

theorem marked_named_fresh_preimage (state : ConstructionState) (token incoming selected : Nat) (snapshot : PendingDestination)
    (index oldIncoming oldSelected : Nat) (oldSnapshot : PendingDestination)
    (ticket : (state.exitReservations.set! token (.active (.named .ready) incoming selected snapshot))[index]? =
      some (.active .fresh oldIncoming oldSelected oldSnapshot)) :
    state.exitReservations[index]? = some (.active .fresh oldIncoming oldSelected oldSnapshot) := by
  by_cases same : token = index
  · subst index
    by_cases inside : token < state.exitReservations.size
    · simp [Array.set!_eq_setIfInBounds, inside] at ticket
    · simp [Array.set!_eq_setIfInBounds, inside] at ticket ⊢
  · simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, same] using ticket

theorem mark_named_source_state (state after : ConstructionState) (token incoming selected : Nat)
    (snapshot : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active (.named .awaitingSource) incoming selected snapshot))
    (valid : OwnershipSourceState state) (marked : markNamedReservation token state = .ok () after) :
    OwnershipSourceState after := by
  obtain ⟨next, same⟩ := mark_named_exact_update state after token incoming selected snapshot ticket marked
  subst after
  let after := { state with exitReservations := state.exitReservations.set! token (.active (.named .ready) incoming selected next) }
  have lifecycle := markNamedReservation_lifecycle token state valid.structural.1.1
  rw [marked] at lifecycle
  have freshBefore (index oldIncoming oldSelected : Nat) (oldSnapshot : PendingDestination)
      (found : after.exitReservations[index]? = some (.active .fresh oldIncoming oldSelected oldSnapshot)) :=
    marked_named_fresh_preimage state token incoming selected next index oldIncoming oldSelected oldSnapshot found
  have aliases : LiveFreshReservationSuccessorRoles after := by
    intro index oldIncoming oldSelected node oldSnapshot row found path present
    exact valid.aliases index oldIncoming oldSelected node oldSnapshot row (freshBefore index oldIncoming oldSelected oldSnapshot found)
      (DestinationSuccessorPath.congr (before := after) (after := state) rfl path) present
  have resumption : ResumptionReservationRoles after := by
    intro key saved present index oldIncoming oldSelected oldSnapshot found resolved
    exact valid.resumptionRoles key saved present index oldIncoming oldSelected oldSnapshot
      (freshBefore index oldIncoming oldSelected oldSnapshot found)
      ((destinationCurrent_congr_tables state after rfl rfl oldSelected).symm.trans resolved)
  have links : ConstructionOwnershipLinks after := by
    refine ⟨lifecycle.1, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · exact valid.structural.1.2.1.2.1
    · intro index oldIncoming oldSelected oldSnapshot found
      exact valid.structural.1.2.1.2.2.1.1 index oldIncoming oldSelected oldSnapshot (freshBefore index oldIncoming oldSelected oldSnapshot found)
    · exact valid.structural.1.2.1.2.2.1.2
    · intro index oldIncoming oldSelected oldSnapshot found
      exact valid.structural.1.2.1.2.2.2.1 index oldIncoming oldSelected oldSnapshot (freshBefore index oldIncoming oldSelected oldSnapshot found)
    · intro index oldIncoming oldSelected oldSnapshot currentRow found
      exact valid.structural.1.2.1.2.2.2.2.1 index oldIncoming oldSelected oldSnapshot currentRow (freshBefore index oldIncoming oldSelected oldSnapshot found)
    · intro index oldIncoming oldSelected oldSnapshot found
      exact valid.structural.1.2.1.2.2.2.2.2.1 index oldIncoming oldSelected oldSnapshot (freshBefore index oldIncoming oldSelected oldSnapshot found)
    · exact valid.structural.1.2.1.2.2.2.2.2.2
  have authority : SupportedReplacementAuthority after := by
    intro id parent selectedRow found use supported
    exact valid.structural.1.2.2.1 id parent selectedRow found use (replacementSupported_congr_destinations after state rfl id supported)
  have backing : ResumptionBackingSources after := valid.structural.1.2.2.2.1
  have unsupported : UnsupportedResumptionKeys after := by
    intro id saved found supported
    exact valid.structural.1.2.2.2.2.1 id saved found (replacementSupported_congr_destinations after state rfl id supported)
  have currentRoles : LiveFreshReservationRoles after := liveFreshReservationSuccessorRoles_current after aliases
  have rawRoles : LiveFreshReservationRawRoles after := liveFreshReservationSuccessorRoles_raw after aliases
  exact ⟨⟨⟨lifecycle, links, authority, backing, unsupported, currentRoles⟩, valid.structural.2.1, rawRoles⟩,
    aliases, valid.inactiveKeys, resumption⟩

#print axioms mark_named_source_state
#print axioms mark_named_exact_update
#print axioms mark_named_lifecycle_and_frame

end Goose.Proofs.ConstructionAcceptedExecution
