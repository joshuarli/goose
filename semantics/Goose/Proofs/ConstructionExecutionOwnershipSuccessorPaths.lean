import Goose.Proofs.ConstructionExecutionOwnershipLiveFreshRows

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

inductive DestinationSuccessorPath (state : ConstructionState) : DestinationId → DestinationId → Prop
  | refl (id : DestinationId) : DestinationSuccessorPath state id id
  | next {start middle finish : DestinationId} :
      state.destinationSuccessors.lookup start = some middle →
      DestinationSuccessorPath state middle finish → DestinationSuccessorPath state start finish

theorem DestinationSuccessorPath.trans {state : ConstructionState} {first middle last : DestinationId}
    (firstPath : DestinationSuccessorPath state first middle) (suffix : DestinationSuccessorPath state middle last) :
    DestinationSuccessorPath state first last := by
  induction firstPath with
  | refl => exact suffix
  | next edge _ previous => exact .next edge (previous suffix)

theorem DestinationSuccessorPath.congr {before after : ConstructionState}
    (successors : after.destinationSuccessors = before.destinationSuccessors)
    {first last : DestinationId} (path : DestinationSuccessorPath before first last) :
    DestinationSuccessorPath after first last := by
  induction path with
  | refl => exact .refl _
  | next edge _ previous => exact .next (by simpa only [successors] using edge) previous

theorem DestinationSuccessorPath.bound {state : ConstructionState}
    (valid : DestinationSuccessorsValid state) {first last : DestinationId}
    (path : DestinationSuccessorPath state first last) (inside : first < state.destinations.size) :
    last < state.destinations.size := by
  induction path with
  | refl => exact inside
  | next edge _ previous => exact previous (valid _ _ edge).2

theorem destinationCurrentSteps_successorPath (fuel : Nat) (state : ConstructionState)
    (incoming current : DestinationId) (resolved : destinationCurrentSteps fuel state incoming = .ok current) :
    DestinationSuccessorPath state incoming current := by
  induction fuel generalizing incoming with
  | zero => simp only [destinationCurrentSteps_zero] at resolved; cases resolved
  | succ fuel previous =>
      rw [destinationCurrentSteps_succ] at resolved
      split at resolved
      · cases edge : state.destinationSuccessors.lookup incoming with
        | none =>
            simp only [edge, Except.ok.injEq] at resolved
            subst current
            exact .refl _
        | some next =>
            simp only [edge] at resolved
            split at resolved
            · exact .next edge (previous next resolved)
            · cases resolved
      · cases resolved

theorem destinationCurrent_successorPath (state : ConstructionState) (incoming current : DestinationId)
    (resolved : destinationCurrent state incoming = .ok current) :
    DestinationSuccessorPath state incoming current :=
  destinationCurrentSteps_successorPath _ state incoming current resolved

def LiveFreshReservationSuccessorRoles (state : ConstructionState) : Prop :=
  ∀ (token : ExitReservationId) (incoming reserved node : DestinationId) (snapshot selected : PendingDestination),
    state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
    DestinationSuccessorPath state reserved node → state.destinations[node]? = some selected →
    if reserved = snapshot.capability.id then
      selected.use = snapshot.use ∧ SnapshotBackingAgrees snapshot selected
    else selected.use = .replacement snapshot.capability.id ∧ selected.backing = snapshot.backing

theorem liveFreshReservationSuccessorRoles_raw (state : ConstructionState)
    (valid : LiveFreshReservationSuccessorRoles state) : LiveFreshReservationRawRoles state := by
  intro token incoming reserved snapshot selected ticket present
  exact valid token incoming reserved reserved snapshot selected ticket (.refl _) present

theorem liveFreshReservationSuccessorRoles_current (state : ConstructionState)
    (valid : LiveFreshReservationSuccessorRoles state) : LiveFreshReservationRoles state := by
  intro token incoming reserved current snapshot selected ticket resolved present
  exact valid token incoming reserved current snapshot selected ticket
    (destinationCurrent_successorPath state reserved current resolved) present

theorem initial_liveFreshReservationSuccessorRoles : LiveFreshReservationSuccessorRoles .initial := by
  intro token incoming reserved node snapshot selected ticket
  simp [ConstructionState.initial] at ticket

theorem liveFreshReservationSuccessorRoles_sourceExtension (before after : ConstructionState)
    (valid : ReservationLifecycleInvariant before) (successorValid : DestinationSuccessorsValid before)
    (source : OwnershipSourceExtension before after)
    (successors : after.destinationSuccessors = before.destinationSuccessors)
    (tickets : ∀ (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot : PendingDestination),
      after.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      before.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (roles : LiveFreshReservationSuccessorRoles before) : LiveFreshReservationSuccessorRoles after := by
  intro token incoming reserved node snapshot selected ticket path present
  have oldTicket := tickets token incoming reserved snapshot ticket
  have oldPath := path.congr successors.symm
  have inside := oldPath.bound successorValid (valid.2.active token .fresh incoming reserved snapshot oldTicket).2.1
  let oldRow := before.destinations[node]
  have oldPresent : before.destinations[node]? = some oldRow := Array.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩
  obtain ⟨actual, actualPresent, sameUse, sameBacking⟩ := source node oldRow oldPresent
  have same : actual = selected := Option.some.inj (actualPresent.symm.trans present)
  subst actual
  have oldRoles := roles token incoming reserved node snapshot oldRow oldTicket oldPath oldPresent
  by_cases direct : reserved = snapshot.capability.id
  · simp only [ite_eq_left direct] at oldRoles ⊢
    exact ⟨sameUse.trans oldRoles.1,
      snapshotBackingAgrees_source snapshot oldRow selected oldRoles.1 oldRoles.2 sameBacking⟩
  · simp only [ite_eq_right direct] at oldRoles ⊢
    refine ⟨sameUse.trans oldRoles.1, ?_⟩
    simp only [OwnershipLinkBacking, oldRoles.1] at sameBacking
    exact sameBacking.trans oldRoles.2

end Goose.Proofs.ConstructionExecutionOwnership
