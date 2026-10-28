import Goose.Proofs.ConstructionAcceptedReturnedCall
import Goose.Proofs.ExitExecutionLandedChannels

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem finishConstructCall_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (incoming id : Nat) (ty : Ty) (origin : OriginId)
    (action : EvalM (List Carrier)) (before after : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (channels : activation.channels = [.construct incoming])
    (done : action before = .ok [.completed id] after)
    (world : AcceptedWorld config initialized after
      (.returned [.completed id] :: .callChannels activation [] :: ambient) types live regions pending)
    (current : destinationCurrent after.construction incoming = .ok id)
    (normalized : NormalizedCompletedCarrier after ty id) :
    let final := { after with activations := after.activations.filter (fun current => current.act != activation.act) }
    (finishActivation config.layout activation [ty] origin action >>= fun carriers =>
      deliverCarriers fuel config.layout [.construct incoming] carriers origin) before = .ok [.completed id] final ∧
    AcceptedWorld config initialized final (.returned [.completed id] :: ambient) types live regions pending := by
  let final := { after with activations := after.activations.filter (fun current => current.act != activation.act) }
  have finalNormalized : NormalizedCompletedCarrier final ty id := NormalizedCompletedCarrier.of_construction_eq (before := after) (after := final) rfl normalized
  have landed : LandedResultChannels final [.construct incoming] [ty] [.completed id] :=
    .cons (.construct incoming id ty current finalNormalized) .nil
  have finished := landed.finishChannels config.layout origin
  constructor
  · simp [finishActivation, done, channels, finished, bind, deliverCarriers, pure, final]
  · exact world.finishReturnedCall config initialized after activation [.completed id] ambient types live regions pending

#print axioms finishConstructCall_world
end Goose.Proofs.ConstructionAcceptedExecution
