import Goose.Proofs.OwnershipAmbientContext
import Goose.Proofs.ConstructionExecutionOwnershipSuccessorResolution

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

theorem OwnershipSourceExtension.refl (state : ConstructionState) : OwnershipSourceExtension state state := by
  intro id row present
  exact ⟨row, present, rfl, by cases use : row.use <;> simp [OwnershipLinkBacking, use]⟩

theorem snapshotBackingAgrees_source (snapshot before after : PendingDestination)
    (use : before.use = snapshot.use) (backing : SnapshotBackingAgrees snapshot before)
    (extension : OwnershipLinkBacking before after) : SnapshotBackingAgrees snapshot after := by
  cases kind : snapshot.use with
  | receiver => simp only [SnapshotBackingAgrees, kind]
  | child parent =>
      have actual : before.use = .child parent := use.trans kind
      simp only [SnapshotBackingAgrees, kind] at backing ⊢
      simp only [OwnershipLinkBacking, actual] at extension
      exact backing.trans extension.symm
  | replacement parent =>
      have actual : before.use = .replacement parent := use.trans kind
      simp only [SnapshotBackingAgrees, kind] at backing ⊢
      simp only [OwnershipLinkBacking, actual] at extension
      exact backing.trans extension.symm

theorem liveFreshReservationRoles_sourceExtension (before after : ConstructionState)
    (valid : ReservationLifecycleInvariant before) (successorValid : DestinationSuccessorsValid before)
    (source : OwnershipSourceExtension before after)
    (successors : after.destinationSuccessors = before.destinationSuccessors)
    (size : before.destinations.size ≤ after.destinations.size)
    (tickets : ∀ (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot : PendingDestination),
      after.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      before.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (roles : LiveFreshReservationRoles before) : LiveFreshReservationRoles after := by
  intro token incoming reserved current snapshot selected ticket resolved present
  have oldTicket := tickets token incoming reserved snapshot ticket
  have allocated := (valid.2.active token .fresh incoming reserved snapshot oldTicket).2.1
  obtain ⟨oldCurrent, oldResolved, _, inside, _⟩ := destinationCurrent_total before successorValid reserved allocated
  have extended := destinationCurrent_extension before after successors size reserved oldCurrent oldResolved
  have same : current = oldCurrent := Except.ok.inj (resolved.symm.trans extended)
  subst current
  let oldRow := before.destinations[oldCurrent]
  have oldPresent : before.destinations[oldCurrent]? = some oldRow :=
    Array.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩
  obtain ⟨actual, actualPresent, sameUse, sameBacking⟩ := source oldCurrent oldRow oldPresent
  have same : actual = selected := Option.some.inj (actualPresent.symm.trans present)
  subst actual
  have oldRoles := roles token incoming reserved oldCurrent snapshot oldRow oldTicket oldResolved oldPresent
  by_cases direct : reserved = snapshot.capability.id
  · simp only [ite_eq_left direct] at oldRoles ⊢
    exact ⟨sameUse.trans oldRoles.1,
      snapshotBackingAgrees_source snapshot oldRow selected oldRoles.1 oldRoles.2 sameBacking⟩
  · simp only [ite_eq_right direct] at oldRoles ⊢
    refine ⟨sameUse.trans oldRoles.1, ?_⟩
    simp only [OwnershipLinkBacking, oldRoles.1] at sameBacking
    exact sameBacking.trans oldRoles.2


def LiveFreshReservationRawRoles (state : ConstructionState) : Prop :=
  ∀ (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot selected : PendingDestination),
    state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
    state.destinations[reserved]? = some selected →
    if reserved = snapshot.capability.id then
      selected.use = snapshot.use ∧ SnapshotBackingAgrees snapshot selected
    else selected.use = .replacement snapshot.capability.id ∧ selected.backing = snapshot.backing

theorem liveFreshReservationRawRoles_sourceExtension (before after : ConstructionState)
    (valid : ReservationLifecycleInvariant before) (source : OwnershipSourceExtension before after)
    (tickets : ∀ (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot : PendingDestination),
      after.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      before.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (roles : LiveFreshReservationRawRoles before) : LiveFreshReservationRawRoles after := by
  intro token incoming reserved snapshot selected ticket present
  have oldTicket := tickets token incoming reserved snapshot ticket
  have allocated := (valid.2.active token .fresh incoming reserved snapshot oldTicket).2.1
  let oldRow := before.destinations[reserved]
  have oldPresent : before.destinations[reserved]? = some oldRow :=
    Array.getElem?_eq_some_iff.mpr ⟨allocated, rfl⟩
  obtain ⟨actual, actualPresent, sameUse, sameBacking⟩ := source reserved oldRow oldPresent
  have same : actual = selected := Option.some.inj (actualPresent.symm.trans present)
  subst actual
  have oldRoles := roles token incoming reserved snapshot oldRow oldTicket oldPresent
  by_cases direct : reserved = snapshot.capability.id
  · simp only [ite_eq_left direct] at oldRoles ⊢
    exact ⟨sameUse.trans oldRoles.1,
      snapshotBackingAgrees_source snapshot oldRow selected oldRoles.1 oldRoles.2 sameBacking⟩
  · simp only [ite_eq_right direct] at oldRoles ⊢
    refine ⟨sameUse.trans oldRoles.1, ?_⟩
    simp only [OwnershipLinkBacking, oldRoles.1] at sameBacking
    exact sameBacking.trans oldRoles.2

theorem liveFreshReservationRawRoles_metadata (before after : ConstructionState)
    (rows : after.destinations = before.destinations)
    (tickets : ∀ (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot : PendingDestination),
      after.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      before.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (roles : LiveFreshReservationRawRoles before) : LiveFreshReservationRawRoles after := by
  intro token incoming reserved snapshot selected ticket present
  exact roles token incoming reserved snapshot selected (tickets token incoming reserved snapshot ticket)
    (by simpa only [rows] using present)

theorem initial_liveFreshReservationRawRoles : LiveFreshReservationRawRoles .initial := by
  intro token incoming reserved snapshot selected ticket
  simp [ConstructionState.initial] at ticket

def OwnershipSourceStructural (state : ConstructionState) : Prop :=
  OwnershipStructural state ∧ DestinationSuccessorsValid state ∧ LiveFreshReservationRawRoles state

theorem initial_ownershipSourceStructural : OwnershipSourceStructural .initial :=
  ⟨initial_ownershipStructural, initial_destination_successors, initial_liveFreshReservationRawRoles⟩

end Goose.Proofs.ConstructionExecutionOwnership
