import Goose.Proofs.ConstructionAcceptedBytePublication
import Goose.Proofs.ConstructionAcceptedByteSource
import Goose.Proofs.ExitExecutionReceiverReadiness
import Goose.Proofs.ConstructionAcceptedState
import Goose.Proofs.ExitExecutionLiveCarriers

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ExitExecution
open Goose.Proofs.ConstructionExecutionOwnership

theorem accepted_byte_return_carrier_backed (fuel : Nat) (config : EvalConfig)
    (initialized : Nat) (environment : RuntimeActivation) (bytes : List UInt8)
    (origin : Goose.Core.OriginId) (id count : Nat) (before after : ExecutionState)
    (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (openBacking : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : openBacking.destination.layout = .packed)
    (request : openBacking.destination.capability.request = .value)
    (fits : count + bytes.length < 2 ^ 32)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    CarrierResultBacking config.layout after (.completed id) := by
  obtain ⟨value, sampled, backed⟩ := buildExpr_byteOwner_backing fuel config environment bytes origin id count
    before after openBacking packed request fits world.ownership.source.structural.1.1.1 current executed
  obtain ⟨destination, storage, present, _, _, _, _, _, _, built, _⟩ :=
    buildExpr_byteOwner_geometry fuel config environment bytes origin id count before after
      openBacking packed request fits world.ownership.source.structural.1.1.1 current executed
  exact .completed id (count + bytes.length) destination value present built sampled backed

theorem accepted_byte_receiver_landing_ready (fuel : Nat) (config : EvalConfig)
    (initialized : Nat) (environment : RuntimeActivation) (bytes : List UInt8)
    (origin : Goose.Core.OriginId) (id count : Nat) (before after : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (openBacking : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : openBacking.destination.layout = .packed)
    (request : openBacking.destination.capability.request = .value)
    (receiver : openBacking.destination.use = .receiver)
    (fits : count + bytes.length < 2 ^ 32)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    CarrierResultBacking config.layout after (.completed id) ∧
      Nonempty (ReceivingCarrierLandingReady after id id) ∧
      landCarriersInto origin [.construct id] [.completed id] after = .ok () after := by
  have backed := accepted_byte_return_carrier_backed fuel config initialized environment bytes origin id count
    before after ambient types live regions pending world openBacking packed request fits current executed
  obtain ⟨destination, storage, present, _, _, _, _, _, use, built, _⟩ :=
    buildExpr_byteOwner_geometry fuel config environment bytes origin id count before after
      openBacking packed request fits world.ownership.source.structural.1.1.1 current executed
  have source := buildExpr_bytes_sourceState fuel config environment id (.varr (.int .u8)) bytes origin
    before after openBacking.destination count world.ownership.source current openBacking.present openBacking.opened executed
  have terminal := destinationSuccessorKeysInactive_built_terminal after.construction source.inactiveKeys id
    destination present (count + bytes.length) built
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have resolved : destinationCurrent after.construction id = .ok id := by
    simp only [destinationCurrent_result, destinationCurrentSteps_succ, inside, ↓reduceIte, terminal]
  let ready : ReceivingCarrierLandingReady after id id :=
    ⟨id, destination, destination, resolved, present, present, .refl _,
      .receiver (use.trans receiver), Nat.le_refl _⟩
  exact ⟨backed, ⟨ready⟩, landCarriersInto_current origin after id id ready rfl⟩

#print axioms accepted_byte_receiver_landing_ready
#print axioms accepted_byte_return_carrier_backed

end Goose.Proofs.ConstructionAcceptedExecution
