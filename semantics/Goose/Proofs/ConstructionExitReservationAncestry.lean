import Goose.Proofs.ConstructionExitReservationBacking
import Goose.Proofs.ConstructionAcceptedDestinationAncestry

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

private theorem ancestry_step (rows : Array PendingDestination) (ancestor fuel id : Nat) :
    ancestryWalk rows ancestor (fuel + 1) id =
      if id == ancestor then true else match rows[id]? with
      | none => false
      | some row => match row.use with
        | .receiver => false
        | .child parent | .replacement parent => ancestryWalk rows ancestor fuel parent := rfl

private theorem ancestry_fuel (state : ConstructionState) (ordered : DestinationOwnersOrdered state)
    (ancestor first second id : Nat) (firstBound : id < first) (secondBound : id < second) :
    ancestryWalk state.destinations ancestor first id = ancestryWalk state.destinations ancestor second id := by
  induction first generalizing second id with
  | zero => omega
  | succ first ih =>
    cases second with
    | zero => omega
    | succ second =>
      rw [ancestry_step, ancestry_step]
      split
      · rfl
      · cases found : state.destinations[id]? with
        | none => rfl
        | some row =>
          simp only
          cases use : row.use with
          | receiver => rfl
          | child parent | replacement parent =>
            simp only
            have earlier : parent < id := by simpa only [use] using ordered id row found
            exact ih second parent (Nat.lt_of_lt_of_le earlier (Nat.le_of_lt_succ firstBound))
              (Nat.lt_of_lt_of_le earlier (Nat.le_of_lt_succ secondBound))

private theorem ancestry_source (before after : ConstructionState)
    (ordered : DestinationOwnersOrdered before) (extension : OwnershipSourceExtension before after)
    (ancestor fuel id : Nat) (inside : id < before.destinations.size) :
    ancestryWalk after.destinations ancestor fuel id = ancestryWalk before.destinations ancestor fuel id := by
  induction fuel generalizing id with
  | zero => rfl
  | succ fuel ih =>
    rw [ancestry_step, ancestry_step]
    split
    · rfl
    · let row := before.destinations[id]
      have found : before.destinations[id]? = some row := Array.getElem?_eq_getElem inside
      obtain ⟨newRow, present, use, _⟩ := extension id row found
      simp only [found, present]
      rw [use]
      cases oldUse : row.use with
      | receiver => rfl
      | child parent | replacement parent =>
        have earlier : parent < id := by simpa only [oldUse] using ordered id row found
        exact ih parent (Nat.lt_trans earlier inside)

theorem destinationDescendant_source_old (before after : ConstructionState)
    (ordered : DestinationOwnersOrdered before) (extension : OwnershipSourceExtension before after)
    (size : before.destinations.size ≤ after.destinations.size) (ancestor id : Nat)
    (inside : id < before.destinations.size) :
    destinationDescendant after.destinations ancestor id = destinationDescendant before.destinations ancestor id := by
  rw [destinationDescendant_walk, destinationDescendant_walk]
  rw [ancestry_source before after ordered extension ancestor _ id inside]
  exact ancestry_fuel before ordered ancestor _ _ id (by omega) (by omega)

theorem accepted_open_reservation_old_boundaries (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (history : ReservationReferencesBounded before.construction ambient)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (covered : ∀ id, .completed id ∈ ambient.retained → ∃ frame ∈ pending, .completed id ∈ frame.carriers) :
    OwnershipAmbientBoundaries reserved ambient := by
  obtain ⟨allocated, replacement, appended, source, _, _⟩ :=
    accepted_open_reservation_allocation config initialized before reserved incoming selected token count receiver.destination
      receiver.present receiver.opened current ambient types live regions pending [] [] world reservation
  have fresh := (accepted_fresh_reservation_frames config initialized before reserved incoming token selected
    ambient types live regions pending world reservation [] []).1
  have metadata := openExitReplacement_reservation_frame incoming before.construction world.ownership.source.structural.1.1.1
  rw [replacement] at metadata
  have extension := openExitReplacement_ownership_source incoming before.construction world.ownership.source.structural.1.1.1
  rw [replacement] at extension
  have extensionAfter : OwnershipSourceExtension before.construction reserved := by
    simpa only [ConstructionResult.finalState, appended, OwnershipSourceExtension] using extension
  have map := openExitReplacement_successorMap incoming before.construction
  rw [replacement] at map
  have successors : reserved.destinationSuccessors = before.construction.destinationSuccessors := by
    simpa only [ConstructionResult.finalState, appended] using map
  have size : before.construction.destinations.size ≤ reserved.destinations.size := by
    simpa only [ConstructionResult.finalState, appended] using metadata.destinations
  have oldTickets : ∀ id status, id < before.construction.exitReservations.size →
      reserved.exitReservations[id]? = some status → before.construction.exitReservations[id]? = some status := by
    intro id status bound found
    have tickets : allocated.exitReservations = before.construction.exitReservations := by
      simpa only [ConstructionResult.finalState] using metadata.tickets
    rw [appended] at found
    simpa [tickets, Array.getElem?_push, bound, Nat.ne_of_lt bound] using found
  have allBound := completed_carriers_bounded_by_pending config initialized before ambient types live regions pending world covered
  have transfer : ∀ inner, ReservationReferencesBounded before.construction inner →
      OwnershipAmbientBoundaries before.construction inner →
      (∀ id ∈ completedCarrierIds inner.retained, id < before.construction.destinations.size) →
      OwnershipAmbientBoundaries reserved inner := by
    intro inner
    induction inner with
    | nil => intro _ _ _; trivial
    | cons frame outer ih =>
      intro bounded previous allInside
      have restBounded : ReservationReferencesBounded before.construction outer := by
        intro item member
        exact bounded item (List.mem_cons_of_mem frame member)
      have restInside : ∀ id ∈ completedCarrierIds (OwnershipAmbient.retained outer), id < before.construction.destinations.size := by
        intro id member
        apply allInside id
        simp only [completedCarrierIds, List.mem_filterMap] at member ⊢
        obtain ⟨carrier, found, filtered⟩ := member
        refine ⟨carrier, ?_, filtered⟩
        simp only [OwnershipAmbient.retained, List.flatMap_cons, List.mem_append]
        exact Or.inr found
      refine ⟨?_, ih restBounded previous.2 restInside⟩
      intro id oldIncoming oldSelected resolved snapshot member ticket result retained retainedMember
      have idBound := (bounded frame (by simp)).1 id member
      have old := oldTickets id (.active .fresh oldIncoming oldSelected snapshot) idBound ticket
      have selectedBound := (world.ownership.source.structural.1.1.2.active id .fresh oldIncoming oldSelected snapshot old).2.1
      obtain ⟨oldCurrent, oldResolved, _, _, _⟩ := destinationCurrent_total before.construction
        world.ownership.source.structural.2.1 oldSelected selectedBound
      have next := destinationCurrent_extension before.construction reserved successors size oldSelected oldCurrent oldResolved
      have same := Except.ok.inj (next.symm.trans result)
      subst resolved
      have prior := previous.1 id oldIncoming oldSelected oldCurrent snapshot member old oldResolved retained retainedMember
      rw [destinationDescendant_source_old before.construction reserved world.ownership.source.structural.1.1.1.2.2.2
        extensionAfter size oldCurrent retained (restInside retained retainedMember)]
      exact prior
  exact transfer ambient history world.ownership.retention.boundaries allBound

theorem accepted_open_reservation_boundaries (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (channels : List Channel) (carriers : List Goose.Construct.Carrier)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (history : ReservationReferencesBounded before.construction ambient)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (covered : ∀ id, .completed id ∈ ambient.retained → ∃ frame ∈ pending, .completed id ∈ frame.carriers) :
    OwnershipAmbientBoundaries reserved (.exitChannels [token] channels carriers :: ambient) :=
  ⟨accepted_open_reservation_boundary_from_pending config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world reservation covered,
    accepted_open_reservation_old_boundaries config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world history reservation covered⟩

#print axioms destinationDescendant_source_old
#print axioms accepted_open_reservation_old_boundaries
#print axioms accepted_open_reservation_boundaries

end Goose.Proofs.ConstructionAcceptedExecution
