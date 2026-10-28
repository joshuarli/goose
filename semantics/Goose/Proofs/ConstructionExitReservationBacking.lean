import Goose.Proofs.ConstructionExitReservationBoundary

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem accepted_open_reservation_rooted_backing (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (region : ReceivingRegion) (member : region ∈ regions) (destination : region.destination = incoming)
    (outside : ∀ root, live root → ¬ region.mutableRoots root) :
    RootedBackingState config.layout { before with construction := reserved } live ∧
    ReceivingProtection config.layout { before with construction := reserved } live
      { region with mutableDestinations := selected :: region.mutableDestinations } := by
  have protection := reserve_open_extended_protection config.layout before reserved incoming selected token count
    receiver current reservation live region destination (world.protections region member)
  refine ⟨?_, protection⟩
  constructor
  · intro root isLive value found
    exact protection.observations.backing.values root ⟨isLive, outside root isLive⟩ value found
  · intro root isLive stored found
    exact protection.observations.backing.identities root ⟨isLive, outside root isLive⟩ stored found

#print axioms accepted_open_reservation_rooted_backing

theorem accepted_open_reservation_backed_parts (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (channels : List Channel) (carriers : List Goose.Construct.Carrier)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (history : ReservationReferencesBounded before.construction ambient)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (covered : ∀ id, .completed id ∈ ambient.retained → ∃ frame ∈ pending, .completed id ∈ frame.carriers)
    (region : ReceivingRegion) (member : region ∈ regions) (destination : region.destination = incoming)
    (outside : ∀ root, live root → ¬ region.mutableRoots root) :
    RootedBackingState config.layout { before with construction := reserved } live ∧
    OwnershipSourceState reserved ∧
    OwnershipReservationFrames reserved (.exitChannels [token] channels carriers :: ambient) ∧
    OwnershipRuntimeFrames { before with construction := reserved } (.exitChannels [token] channels carriers :: ambient) ∧
    OwnershipRuntimeIdentities { before with construction := reserved } ∧
    OwnershipCapturedReceivingBounds reserved (.exitChannels [token] channels carriers :: ambient) ∧
    OwnershipCapturedReceivingFrames reserved (.exitChannels [token] channels carriers :: ambient) ∧
    RetainedOutsideTickets reserved [token] ambient.retained ∧
    ReceivingProtection config.layout { before with construction := reserved } live
      { region with mutableDestinations := selected :: region.mutableDestinations } := by
  have backed := accepted_open_reservation_rooted_backing config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending world reservation region member destination outside
  have parts := accepted_open_reservation_world_parts config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending channels carriers world history reservation covered region member destination
  exact ⟨backed.1, parts⟩

#print axioms accepted_open_reservation_backed_parts

end Goose.Proofs.ConstructionAcceptedExecution
