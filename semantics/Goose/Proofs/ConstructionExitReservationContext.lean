import Goose.Proofs.ExitExecutionOwnedReceiptSetup
import Goose.Proofs.ConstructionAcceptedState

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem accepted_fresh_reservation_frames (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming token selected : Nat)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (channels : List Channel) (carriers : List Goose.Construct.Carrier) :
    token = before.construction.exitReservations.size ∧
    (∀ id status, before.construction.exitReservations[id]? = some status →
      id ≠ token ∧ reserved.exitReservations[id]? = some status) ∧
    OwnershipReservationFrames reserved (.exitChannels [token] channels carriers :: ambient) ∧
    OwnershipRuntimeFrames { before with construction := reserved } (.exitChannels [token] channels carriers :: ambient) ∧
    OwnershipRuntimeIdentities { before with construction := reserved } := by
  obtain ⟨fresh, snapshot, pushed⟩ := reserveExitDestination_active_push incoming .newValue before.construction reserved
    token selected world.ownership.source.structural.1.1 reservation
  refine ⟨fresh, ?_, ?_, ?_, ⟨world.ownership.identities.activations, world.ownership.identities.breaks⟩⟩
  · intro id status present
    have bound := (Array.getElem?_eq_some_iff.mp present).1
    have ne : id ≠ token := by rw [fresh]; exact Nat.ne_of_lt bound
    refine ⟨ne, ?_⟩
    simpa [pushed, Array.getElem?_push, bound, Nat.ne_of_lt bound] using present
  · intro id status present needed
    by_cases same : id = token
    · subst id
      exact ⟨.exitChannels [token] channels carriers, by simp, by simp [OwnershipAmbientFrame.tickets]⟩
    · have original : before.construction.exitReservations[id]? = some status := by
        rw [pushed] at present
        have ne : id ≠ before.construction.exitReservations.size := by simpa only [fresh] using same
        simpa [Array.getElem?_push, ne] using present
      obtain ⟨owner, member, owns⟩ := world.ownership.reservations id status original needed
      exact ⟨owner, List.mem_cons_of_mem _ member, owns⟩
  · exact ⟨world.ownership.runtime.activations, world.ownership.runtime.breaks⟩

#print axioms accepted_fresh_reservation_frames

end Goose.Proofs.ConstructionAcceptedExecution
