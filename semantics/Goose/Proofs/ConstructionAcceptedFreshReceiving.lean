import Goose.Proofs.ConstructionAcceptedConstructActivation
import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsCleanupAncestry

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionRepresentation

theorem newest_destination_within_successorFrames (state : ConstructionState) (ambient : OwnershipAmbient) (id : Nat)
    (newest : id + 1 = state.destinations.size) (ordered : DestinationOwnersOrdered state) :
    OwnershipReceivingWithinSuccessorFrames state ambient id := by
  intro frame member token owned incoming reserved snapshot node ticket successors ancestry
  cases ancestry with
  | refl => rfl
  | step node parent ancestor row present use path =>
    have parentLe := path.le ordered
    have parentBefore : parent < node := by simpa only [use] using ordered node row present
    have nodeInside := (Array.getElem?_eq_some_iff.mp present).1
    have lower : id < node := Nat.lt_of_le_of_lt parentLe parentBefore
    have upper : node < id + 1 := by rw [newest]; exact nodeInside
    omega

theorem acceptedWorld_pushNewestConstructActivation (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (activation : RuntimeActivation) (id : Nat)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (identifier : activation.act = state.nextAct) (channels : activation.channels = [.construct id])
    (newest : id + 1 = state.construction.destinations.size)
    (current : destinationCurrent state.construction id = .ok id) :
    AcceptedWorld config initialized
      { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      (.callChannels activation [] :: ambient) types live regions pending := by
  apply acceptedWorld_pushConstructActivation_withReceiving config initialized state ambient types live regions pending activation id world identifier channels
    (by omega)
  intro receiving resolved
  have same : receiving = id := Except.ok.inj (resolved.symm.trans current)
  subst receiving
  exact newest_destination_within_successorFrames state.construction ambient id newest world.ownership.source.structural.1.1.1.2.2.2

#print axioms acceptedWorld_pushNewestConstructActivation
#print axioms newest_destination_within_successorFrames
end Goose.Proofs.ConstructionAcceptedExecution
