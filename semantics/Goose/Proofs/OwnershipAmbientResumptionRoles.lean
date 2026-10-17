import Goose.Proofs.OwnershipAmbientFrontiers
import Goose.Proofs.ConstructionExecutionOwnershipLiveFreshRows

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct
open Goose.Core (DestinationId)

def FreshReservationSnapshotRole (reserved : DestinationId) (snapshot saved : PendingDestination) : Prop :=
  if reserved = snapshot.capability.id then
    saved.use = snapshot.use ∧ SnapshotBackingAgrees snapshot saved
  else saved.use = .replacement snapshot.capability.id ∧ saved.backing = snapshot.backing

def ResumptionReservationRoles (state : ConstructionState) : Prop :=
  ∀ (key : DestinationId) (saved : PendingDestination), state.destinationResumptions.lookup key = some saved →
    ∀ (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot : PendingDestination),
      state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      destinationCurrent state reserved = .ok key → FreshReservationSnapshotRole reserved snapshot saved

theorem initial_resumptionReservationRoles : ResumptionReservationRoles .initial := by
  intro key saved present
  simp [ConstructionState.initial] at present

theorem snapshotBackingAgrees_shared_row (first second current : PendingDestination)
    (sameUse : first.use = second.use)
    (firstBacking : SnapshotBackingAgrees first current)
    (secondBacking : SnapshotBackingAgrees second current) : SnapshotBackingAgrees first second := by
  cases use : first.use with
  | receiver => simp only [SnapshotBackingAgrees, use]
  | child parent =>
      have secondUse : second.use = .child parent := sameUse.symm.trans use
      simp only [SnapshotBackingAgrees, use, secondUse] at firstBacking secondBacking ⊢
      exact firstBacking.trans secondBacking.symm
  | replacement parent =>
      have secondUse : second.use = .replacement parent := sameUse.symm.trans use
      simp only [SnapshotBackingAgrees, use, secondUse] at firstBacking secondBacking ⊢
      exact firstBacking.trans secondBacking.symm

theorem freshReservationSnapshotRole_shared_row (reserved : DestinationId) (snapshot saved current : PendingDestination)
    (savedUse : current.use = saved.use) (savedBacking : SnapshotBackingAgrees saved current)
    (role : FreshReservationSnapshotRole reserved snapshot current) : FreshReservationSnapshotRole reserved snapshot saved := by
  by_cases direct : reserved = snapshot.capability.id
  · simp only [FreshReservationSnapshotRole, ite_eq_left direct] at role ⊢
    have sameUse : saved.use = snapshot.use := savedUse.symm.trans role.1
    exact ⟨sameUse, snapshotBackingAgrees_shared_row snapshot saved current sameUse.symm role.2 savedBacking⟩
  · simp only [FreshReservationSnapshotRole, ite_eq_right direct] at role ⊢
    have sameUse : saved.use = .replacement snapshot.capability.id := savedUse.symm.trans role.1
    simp only [SnapshotBackingAgrees, sameUse] at savedBacking
    exact ⟨sameUse, savedBacking.trans role.2⟩

theorem liveFreshReservationRoles_direct_shared_snapshot (state : ConstructionState)
    (roles : LiveFreshReservationRoles state)
    (ownToken : ExitReservationId) (ownIncoming ownReserved selected : DestinationId)
    (saved current : PendingDestination)
    (ownTicket : state.exitReservations[ownToken]? = some (.active .fresh ownIncoming ownReserved saved))
    (ownCurrent : destinationCurrent state ownReserved = .ok selected)
    (present : state.destinations[selected]? = some current) (direct : ownReserved = saved.capability.id)
    (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok selected) :
    FreshReservationSnapshotRole reserved snapshot saved := by
  have own := roles ownToken ownIncoming ownReserved selected saved current ownTicket ownCurrent present
  simp only [ite_eq_left direct] at own
  exact freshReservationSnapshotRole_shared_row reserved snapshot saved current own.1 own.2
    (roles token incoming reserved selected snapshot current ticket resolved present)

theorem resumptionReservationRoles_metadata (before after : ConstructionState)
    (rows : after.destinations = before.destinations)
    (successors : after.destinationSuccessors = before.destinationSuccessors)
    (resumptions : after.destinationResumptions = before.destinationResumptions)
    (tickets : ∀ (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot : PendingDestination),
      after.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      before.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (roles : ResumptionReservationRoles before) : ResumptionReservationRoles after := by
  intro key saved present token incoming reserved snapshot ticket resolved
  exact roles key saved (by simpa only [resumptions] using present) token incoming reserved snapshot
    (tickets token incoming reserved snapshot ticket)
    (by simpa only [destinationCurrent_congr_tables before after rows successors] using resolved)

theorem resumptionReservationRoles_direct_insert (state : ConstructionState)
    (roles : LiveFreshReservationRoles state) (savedRoles : ResumptionReservationRoles state)
    (token : ExitReservationId) (incoming reserved selected : DestinationId) (saved current : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved saved))
    (resolved : destinationCurrent state reserved = .ok selected)
    (present : state.destinations[selected]? = some current) (direct : reserved = saved.capability.id) :
    ResumptionReservationRoles { state with
      exitReservations := state.exitReservations.set! token .restored
      destinationResumptions := (selected, saved) :: state.destinationResumptions } := by
  intro key actual atKey index actualIncoming actualReserved snapshot actualTicket actualCurrent
  have original : state.exitReservations[index]? = some (.active .fresh actualIncoming actualReserved snapshot) := by
    by_cases same : token = index
    · subst index
      have inside : token < state.exitReservations.size := by
        simpa only [Array.size_set!] using (Array.getElem?_eq_some_iff.mp actualTicket).1
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside] at actualTicket
      simp at actualTicket
    · simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same] using actualTicket
  have currentQuery : destinationCurrent state actualReserved = .ok key := by
    simpa only [destinationCurrent_congr_tables state
      { state with
        exitReservations := state.exitReservations.set! token .restored
        destinationResumptions := (selected, saved) :: state.destinationResumptions } rfl rfl] using actualCurrent
  by_cases sameKey : selected = key
  · subst key
    have sameSaved : saved = actual := by simpa [List.lookup] using atKey
    subst actual
    exact liveFreshReservationRoles_direct_shared_snapshot state roles token incoming reserved selected saved current
      ticket resolved present direct index actualIncoming actualReserved snapshot original currentQuery
  · have old : state.destinationResumptions.lookup key = some actual := by
      simpa [List.lookup, beq_eq_false_iff_ne.mpr (Ne.symm sameKey)] using atKey
    exact savedRoles key actual old index actualIncoming actualReserved snapshot original currentQuery

theorem resumptionReservationRoles_extension (before after : ConstructionState)
    (lifecycle : Goose.Proofs.ConstructionExecutionProtocol.ReservationLifecycleInvariant before)
    (successorsValid : DestinationSuccessorsValid before)
    (successors : after.destinationSuccessors = before.destinationSuccessors)
    (size : before.destinations.size ≤ after.destinations.size)
    (resumptions : after.destinationResumptions = before.destinationResumptions)
    (tickets : ∀ (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot : PendingDestination),
      after.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      before.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (roles : ResumptionReservationRoles before) : ResumptionReservationRoles after := by
  intro key saved present token incoming reserved snapshot ticket resolved
  have original := tickets token incoming reserved snapshot ticket
  have allocated := (lifecycle.2.active token .fresh incoming reserved snapshot original).2.1
  obtain ⟨oldCurrent, oldResolved, _, _, _⟩ := destinationCurrent_total before successorsValid reserved allocated
  have extended := destinationCurrent_extension before after successors size reserved oldCurrent oldResolved
  have same : key = oldCurrent := Except.ok.inj (resolved.symm.trans extended)
  subst key
  exact roles oldCurrent saved (by simpa only [resumptions] using present) token incoming reserved snapshot original oldResolved

#print axioms resumptionReservationRoles_extension
#print axioms freshReservationSnapshotRole_shared_row
#print axioms liveFreshReservationRoles_direct_shared_snapshot
#print axioms resumptionReservationRoles_direct_insert
#print axioms resumptionReservationRoles_metadata

end Goose.Proofs.ConstructionExecutionOwnership
