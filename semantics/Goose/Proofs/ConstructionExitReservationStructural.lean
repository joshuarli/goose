import Goose.Proofs.ConstructionExitReservationResumptions

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem accepted_open_reservation_links (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved) :
    ReservationLifecycleInvariant reserved ∧ ConstructionOwnershipLinks reserved := by
  obtain ⟨allocated, replacement, appended, source, _, _⟩ :=
    accepted_open_reservation_allocation config initialized before reserved incoming selected token count receiver.destination
      receiver.present receiver.opened current ambient types live regions pending [] [] world reservation
  have lifecycle := reserveExitDestination_reservation_lifecycle incoming .newValue before.construction world.ownership.source.structural.1.1
  rw [reservation] at lifecycle
  have fresh := reserve_open_replacement_fresh before.construction reserved incoming selected token count receiver.destination receiver.storage
    receiver.present receiver.opened receiver.bytes current reservation
  have indexed : receiver.destination.capability.id = incoming :=
    world.ownership.source.structural.1.1.1.2.1 incoming receiver.destination receiver.present
  have distinct : selected ≠ receiver.destination.capability.id := by
    rw [indexed, fresh]
    exact Nat.ne_of_gt (Array.getElem?_eq_some_iff.mp receiver.present).1
  have parent := open_replacement_parent_exact before.construction allocated incoming selected (count + 1)
    receiver.destination receiver.present receiver.opened replacement
  have previous := source.structural.1.2.1
  have oldTicket (id : Nat) (otherIncoming otherSelected : Nat) (snapshot : PendingDestination)
      (different : id ≠ allocated.exitReservations.size)
      (ticket : (allocated.exitReservations.push (.active .fresh incoming selected receiver.destination))[id]? =
        some (.active .fresh otherIncoming otherSelected snapshot)) :
      allocated.exitReservations[id]? = some (.active .fresh otherIncoming otherSelected snapshot) := by
    simpa [Array.getElem?_push, different] using ticket
  refine ⟨lifecycle, ?_⟩
  rw [appended]
  refine ⟨source.structural.1.1.1, previous.2.1, ?_, ?_, ?_, ?_, previous.2.2.2.2.2.2⟩
  · constructor
    · intro id oldIncoming oldSelected snapshot ticket
      by_cases new : id = allocated.exitReservations.size
      · subst id
        simp only [Array.getElem?_push, ↓reduceIte] at ticket
        cases ticket
        simp [DestinationForwardLink, receiver.opened]
      · exact previous.2.2.1.1 id oldIncoming oldSelected snapshot (oldTicket id oldIncoming oldSelected snapshot new ticket)
    · exact previous.2.2.1.2
  · intro id oldIncoming oldSelected snapshot ticket
    by_cases new : id = allocated.exitReservations.size
    · subst id
      simp only [Array.getElem?_push, ↓reduceIte] at ticket
      cases ticket
      exact ⟨count + 1, Or.inl receiver.opened⟩
    · exact previous.2.2.2.1 id oldIncoming oldSelected snapshot (oldTicket id oldIncoming oldSelected snapshot new ticket)
  · intro id oldIncoming oldSelected snapshot currentRow active different found n replacementId progress
    by_cases new : id = allocated.exitReservations.size
    · subst id
      simp only [Array.getElem?_push, ↓reduceIte] at active
      cases active
      rw [indexed] at found
      have same := Option.some.inj (found.symm.trans parent)
      subst currentRow
      cases h : receiver.destination
      simp_all
    · exact previous.2.2.2.2.1 id oldIncoming oldSelected snapshot currentRow
        (oldTicket id oldIncoming oldSelected snapshot new active) different found n replacementId progress
  · intro id oldIncoming oldSelected snapshot ticket direct
    by_cases new : id = allocated.exitReservations.size
    · subst id
      simp only [Array.getElem?_push, ↓reduceIte] at ticket
      cases ticket
      exact False.elim (distinct direct)
    · exact previous.2.2.2.2.2.1 id oldIncoming oldSelected snapshot (oldTicket id oldIncoming oldSelected snapshot new ticket) direct

#print axioms accepted_open_reservation_links

theorem accepted_open_reservation_source (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved) :
    OwnershipSourceState reserved := by
  obtain ⟨allocated, replacement, appended, source, _, _⟩ :=
    accepted_open_reservation_allocation config initialized before reserved incoming selected token count receiver.destination
      receiver.present receiver.opened current ambient types live regions pending [] [] world reservation
  obtain ⟨lifecycle, links⟩ := accepted_open_reservation_links config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending world reservation
  obtain ⟨roles, inactive, resumptions⟩ := accepted_open_reservation_source_roles config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending world reservation
  have supportedBefore : ∀ id, ReplacementSupported reserved id → ReplacementSupported allocated id := by
    rw [appended]
    intro id supported
    induction supported with
    | active id row present active => exact .active id row present active
    | parent id parent row present use supported ih => exact .parent id parent row present use ih
  have support : SupportedReplacementAuthority reserved := by
    intro id parent row found use supported
    have oldFound : allocated.destinations[id]? = some row := by simpa only [appended] using found
    obtain ⟨owner, present, backing, phase⟩ := source.structural.1.2.2.1 id parent row oldFound use (supportedBefore id supported)
    exact ⟨owner, by simpa only [appended] using present, backing, phase⟩
  have backing : ResumptionBackingSources reserved := by
    rw [appended]
    exact source.structural.1.2.2.2.1
  have unsupported : UnsupportedResumptionKeys reserved := by
    intro id snapshot found supported
    have oldFound : allocated.destinationResumptions.lookup id = some snapshot := by simpa only [appended] using found
    exact source.structural.1.2.2.2.2.1 id snapshot oldFound (supportedBefore id supported)
  have successors : DestinationSuccessorsValid reserved := by
    rw [appended]
    exact source.structural.2.1
  exact ⟨⟨⟨lifecycle, links, support, backing, unsupported, liveFreshReservationSuccessorRoles_current reserved roles⟩,
    successors, liveFreshReservationSuccessorRoles_raw reserved roles⟩, roles, inactive, resumptions⟩

#print axioms accepted_open_reservation_source

end Goose.Proofs.ConstructionAcceptedExecution
