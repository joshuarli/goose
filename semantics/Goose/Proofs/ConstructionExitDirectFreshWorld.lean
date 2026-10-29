import Goose.Proofs.ConstructionExitDirectFreshContext
import Goose.Proofs.ConstructionExitWaitingWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

theorem direct_fresh_acceptedWorld_pending (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (incoming : Nat) (row : PendingDestination) (carriers : List Goose.Construct.Carrier)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (history : ReservationReferencesBounded before.construction ambient)
    (present : before.construction.destinations[incoming]? = some row) (opened : row.progress = .open 0)
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (separated : ∀ retained ∈ completedCarrierIds ambient.retained,
      destinationDescendant before.construction.destinations incoming retained = false) :
    let token := before.construction.exitReservations.size
    let activated := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.active .fresh incoming incoming row) } }
    AcceptedWorld config initialized activated (.exitChannels [token] [] carriers :: ambient) types live regions pending := by
  let reservation := ExitReservation.active .fresh incoming incoming row
  let activated := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push reservation } }
  have ownership := direct_fresh_context_separated before incoming row ambient carriers world.ownership history present opened current separated
  refine ⟨⟨ownership, world.globals, world.globalTypes, world.layouts, world.typeFrontier,
    world.syntheticFrontier, world.heap, world.objectsRegistered, world.ordinalsRegistered, ?_, ?_, ?_⟩, world.globalLive⟩
  · refine ⟨?_, world.backing.identities⟩
    intro root kept value found
    exact appended_ticket_value_backing config.layout before reservation value (world.backing.values root kept value found)
  · intro region member
    have protection := world.protections region member
    refine ⟨protection.present, ?_, protection.cutoff, protection.landing, protection.authority,
      protection.authorityBound, protection.names⟩
    refine ⟨⟨?_, protection.observations.backing.identities⟩, ?_⟩
    · intro root kept value found
      exact appended_ticket_value_backing config.layout before reservation value (protection.observations.backing.values root kept value found)
    · intro root kept value found stored occurrence
      exact appended_ticket_stored_observation config.layout before reservation region.limit stored
        (protection.observations.observations root kept value found stored occurrence)
  · intro frame member
    exact ⟨appended_ticket_pending_carrier_ready config initialized before ambient types live regions pending reservation world frame member,
      appended_ticket_pending_carrier_backing config initialized before ambient types live regions pending reservation world frame member⟩

theorem direct_fresh_acceptedWorld_separated (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (incoming : Nat) (row : PendingDestination) (carriers : List Goose.Construct.Carrier)
    (world : AcceptedWorld config initialized before ambient types live regions [])
    (history : ReservationReferencesBounded before.construction ambient)
    (present : before.construction.destinations[incoming]? = some row) (opened : row.progress = .open 0)
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (separated : ∀ retained ∈ completedCarrierIds ambient.retained,
      destinationDescendant before.construction.destinations incoming retained = false) :
    let token := before.construction.exitReservations.size
    let activated := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.active .fresh incoming incoming row) } }
    AcceptedWorld config initialized activated (.exitChannels [token] [] carriers :: ambient) types live regions [] := by
  exact direct_fresh_acceptedWorld_pending config initialized before ambient types live regions [] incoming row carriers world history present opened current separated

theorem direct_fresh_acceptedWorld (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (incoming : Nat) (row : PendingDestination) (carriers : List Goose.Construct.Carrier)
    (world : AcceptedWorld config initialized before ambient types live regions [])
    (history : ReservationReferencesBounded before.construction ambient)
    (present : before.construction.destinations[incoming]? = some row) (opened : row.progress = .open 0)
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (noRetained : completedCarrierIds ambient.retained = []) :
    let token := before.construction.exitReservations.size
    let activated := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.active .fresh incoming incoming row) } }
    AcceptedWorld config initialized activated (.exitChannels [token] [] carriers :: ambient) types live regions [] := by
  apply direct_fresh_acceptedWorld_separated config initialized before ambient types live regions incoming row carriers world history present opened current
  intro retained member
  rw [noRetained] at member
  cases member

#print axioms direct_fresh_acceptedWorld_pending
#print axioms direct_fresh_acceptedWorld_separated
#print axioms direct_fresh_acceptedWorld
end Goose.Proofs.ConstructionAcceptedExecution
