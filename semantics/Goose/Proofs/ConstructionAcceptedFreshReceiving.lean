import Goose.Proofs.ConstructionAcceptedConstructActivation
import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsCleanupAncestry

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ExitExecution

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

theorem ancestryWalk_ordered_le (state : ConstructionState) (ordered : DestinationOwnersOrdered state)
    (ancestor fuel id : Nat) (descendant : ancestryWalk state.destinations ancestor fuel id = true) : ancestor ≤ id := by
  induction fuel generalizing id with
  | zero => simp [ancestryWalk] at descendant
  | succ fuel ih =>
    by_cases same : id = ancestor
    · omega
    · simp only [ancestryWalk, beq_iff_eq, same, ↓reduceIte] at descendant
      cases found : state.destinations[id]? with
      | none => simp [found] at descendant
      | some row =>
        cases use : row.use with
        | receiver => simp [found, use] at descendant
        | child parent | replacement parent =>
          have follows : ancestryWalk state.destinations ancestor fuel parent = true := by simpa [found, use] using descendant
          have earlier : parent < id := by simpa [use] using ordered id row found
          exact Nat.le_trans (ih parent follows) (Nat.le_of_lt earlier)

theorem destination_retained_older_outside (state : ConstructionState) (id : Nat) (retained : List Carrier)
    (ordered : DestinationOwnersOrdered state)
    (old : ∀ carrier ∈ completedCarrierIds retained, carrier < id) :
    ∀ carrier ∈ completedCarrierIds retained, destinationDescendant state.destinations id carrier = false := by
  intro carrier member
  cases descendant : destinationDescendant state.destinations id carrier with
  | false => rfl
  | true =>
    have prior := old carrier member
    have le := ancestryWalk_ordered_le state ordered id state.destinations.size carrier (by
      rwa [← destinationDescendant_walk])
    exact False.elim ((Nat.not_lt_of_ge le) prior)

#print axioms ancestryWalk_ordered_le
#print axioms destination_retained_older_outside
#print axioms acceptedWorld_pushNewestConstructActivation
#print axioms newest_destination_within_successorFrames
end Goose.Proofs.ConstructionAcceptedExecution
