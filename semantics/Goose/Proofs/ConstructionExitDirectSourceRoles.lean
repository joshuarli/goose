import Goose.Proofs.ConstructionExitDirectByteLoop
import Goose.Proofs.ConstructionExitReservationStructural

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem direct_fresh_source_roles (state : ConstructionState) (id : Nat) (row : PendingDestination)
    (source : OwnershipSourceState state) (present : state.destinations[id]? = some row)
    (opened : row.progress = .open 0) :
    let reserved := { state with exitReservations := state.exitReservations.push (.active .fresh id id row) }
    LiveFreshReservationSuccessorRoles reserved ∧ DestinationSuccessorKeysInactive reserved ∧
      ResumptionReservationRoles reserved := by
  let reserved := { state with exitReservations := state.exitReservations.push (.active .fresh id id row) }
  have indexed : row.capability.id = id := source.structural.1.1.1.2.1 id row present
  have noEdge : state.destinationSuccessors.lookup id = none :=
    destinationSuccessorKeysInactive_live_terminal state source.inactiveKeys id row present (by simp [opened, activeProgress])
  have noSaved : state.destinationResumptions.lookup id = none := by
    cases found : state.destinationResumptions.lookup id with
    | none => rfl
    | some saved =>
      obtain ⟨other, otherFound, inactive, _⟩ := source.structural.1.2.2.2.1 id saved found
      have same := Option.some.inj (otherFound.symm.trans present)
      subst other
      simp [opened, activeProgress] at inactive
  have oldTicket (token incoming selected : Nat) (snapshot : PendingDestination)
      (old : token ≠ state.exitReservations.size)
      (ticket : reserved.exitReservations[token]? = some (.active .fresh incoming selected snapshot)) :
      state.exitReservations[token]? = some (.active .fresh incoming selected snapshot) := by
    simpa [reserved, Array.getElem?_push, old] using ticket
  have sameCurrent (selected : Nat) : destinationCurrent reserved selected = destinationCurrent state selected := by
    exact destinationCurrent_congr_tables state reserved rfl rfl selected
  refine ⟨?_, ?_, ?_⟩
  · intro token incoming selected node snapshot selectedRow ticket path found
    by_cases fresh : token = state.exitReservations.size
    · subst token
      simp only [reserved, Array.getElem?_push, ↓reduceIte] at ticket
      cases ticket
      have sameNode : node = id := by
        cases path with
        | refl => rfl
        | next edge rest => simp only [reserved, noEdge] at edge; cases edge
      subst node
      have sameRow := Option.some.inj (found.symm.trans present)
      subst selectedRow
      simp [indexed, SnapshotBackingAgrees]
      cases row.use <;> simp
    · exact source.aliases token incoming selected node snapshot selectedRow (oldTicket token incoming selected snapshot fresh ticket) (DestinationSuccessorPath.congr (before := reserved) (after := state) rfl path) found
  · exact source.inactiveKeys
  · intro key saved found token incoming selected snapshot ticket resolved
    by_cases fresh : token = state.exitReservations.size
    · subst token
      simp only [reserved, Array.getElem?_push, ↓reduceIte] at ticket
      cases ticket
      rw [sameCurrent] at resolved
      have path := destinationCurrent_successorPath state id key resolved
      have sameKey : key = id := by
        cases path with
        | refl => rfl
        | next edge rest => rw [noEdge] at edge; cases edge
      subst key
      simp only [reserved, noSaved] at found
      cases found
    · rw [sameCurrent] at resolved
      exact source.resumptionRoles key saved found token incoming selected snapshot (oldTicket token incoming selected snapshot fresh ticket) resolved

theorem direct_fresh_source_state (state : ConstructionState) (id : Nat) (row : PendingDestination)
    (source : OwnershipSourceState state) (present : state.destinations[id]? = some row)
    (opened : row.progress = .open 0) (current : destinationCurrent state id = .ok id) :
    OwnershipSourceState { state with exitReservations := state.exitReservations.push (.active .fresh id id row) } := by
  let reserved := { state with exitReservations := state.exitReservations.push (.active .fresh id id row) }
  have indexed : row.capability.id = id := source.structural.1.1.1.2.1 id row present
  have lifecycle := reserveExitDestination_reservation_lifecycle id .newValue state source.structural.1.1
  rw [reserve_open_zero_direct state id row present opened current] at lifecycle
  have roles := direct_fresh_source_roles state id row source present opened
  have previous := source.structural.1.2.1
  have oldTicket (token incoming selected : Nat) (snapshot : PendingDestination)
      (old : token ≠ state.exitReservations.size)
      (ticket : reserved.exitReservations[token]? = some (.active .fresh incoming selected snapshot)) :
      state.exitReservations[token]? = some (.active .fresh incoming selected snapshot) := by
    simpa [reserved, Array.getElem?_push, old] using ticket
  have links : ConstructionOwnershipLinks reserved := by
    refine ⟨previous.1, previous.2.1, ?_, ?_, ?_, ?_, previous.2.2.2.2.2.2⟩
    · constructor
      · intro token incoming selected snapshot ticket
        by_cases fresh : token = state.exitReservations.size
        · subst token
          simp only [reserved, Array.getElem?_push, ↓reduceIte] at ticket
          cases ticket
          simp [DestinationForwardLink, opened]
        · exact previous.2.2.1.1 token incoming selected snapshot (oldTicket token incoming selected snapshot fresh ticket)
      · exact previous.2.2.1.2
    · intro token incoming selected snapshot ticket
      by_cases fresh : token = state.exitReservations.size
      · subst token
        simp only [reserved, Array.getElem?_push, ↓reduceIte] at ticket
        cases ticket
        exact ⟨0, Or.inl opened⟩
      · exact previous.2.2.2.1 token incoming selected snapshot (oldTicket token incoming selected snapshot fresh ticket)
    · intro token incoming selected snapshot row' ticket different found n replacement progress
      by_cases fresh : token = state.exitReservations.size
      · subst token
        simp only [reserved, Array.getElem?_push, ↓reduceIte] at ticket
        cases ticket
        exact False.elim (different indexed.symm)
      · exact previous.2.2.2.2.1 token incoming selected snapshot row' (oldTicket token incoming selected snapshot fresh ticket) different found n replacement progress
    · intro token incoming selected snapshot ticket direct
      by_cases fresh : token = state.exitReservations.size
      · subst token
        simp only [reserved, Array.getElem?_push, ↓reduceIte] at ticket
        cases ticket
        exact opened
      · exact previous.2.2.2.2.2.1 token incoming selected snapshot (oldTicket token incoming selected snapshot fresh ticket) direct
  have supportBefore : ∀ key, ReplacementSupported reserved key → ReplacementSupported state key := by
    intro key supported
    induction supported with
    | active key row found active => exact .active key row found active
    | parent key parent row found use supported ih => exact .parent key parent row found use ih
  have support : SupportedReplacementAuthority reserved := by
    intro key parent row found use supported
    obtain ⟨owner, ownerFound, backing, phase⟩ := source.structural.1.2.2.1 key parent row found use (supportBefore key supported)
    exact ⟨owner, ownerFound, backing, phase⟩
  have unsupported : UnsupportedResumptionKeys reserved := by
    intro key snapshot found supported
    exact source.structural.1.2.2.2.2.1 key snapshot found (supportBefore key supported)
  exact ⟨⟨⟨lifecycle, links, support, source.structural.1.2.2.2.1, unsupported,
    liveFreshReservationSuccessorRoles_current reserved roles.1⟩, source.structural.2.1,
    liveFreshReservationSuccessorRoles_raw reserved roles.1⟩, roles.1, roles.2.1, roles.2.2⟩

#print axioms direct_fresh_source_state
#print axioms direct_fresh_source_roles

end Goose.Proofs.ConstructionAcceptedExecution
