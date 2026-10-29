import Goose.Proofs.ConstructionExitFreshImmediateCancel
import Goose.Proofs.ConstructionExitFreshCancelStorage
import Goose.Proofs.ConstructionRootedBackingPrefixes

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem allocated_receiver_cancel_rooted (config : EvalConfig) (initialized : Nat) (owner : ActId)
    (ty element : Goose.Construct.Ty) (request : ConstructionRequest) (origin : OriginId) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (elementType : Goose.Construct.elementType ty = some element)
    (created : newDestination config.layout owner ty request origin none knownCount before = .ok id allocated) :
    ∃ reserved final,
      reserveExitDestination id .newValue allocated.construction = .ok (allocated.construction.exitReservations.size, id) reserved ∧
      (do
        cancelExitReservation allocated.construction.exitReservations.size []
        releaseExitReservation allocated.construction.exitReservations.size) reserved = .ok () final ∧
      RootedBackingObservations config.layout { allocated with construction := final } live (storageExtent before) := by
  obtain ⟨reserved, final, reserve, cancelled, rows, tickets⟩ := allocated_receiver_direct_cancel config initialized owner
    ty element request origin knownCount before allocated id ambient types live regions pending world elementType created
  obtain ⟨reserved2, final2, reserve2, cancelled2, storage⟩ := allocated_receiver_cancel_old_storage config initialized owner
    ty element request origin knownCount before allocated id ambient types live regions pending world elementType created
  have sameReserved : reserved2 = reserved := (ConstructionResult.ok.inj (reserve2.symm.trans reserve)).2
  subst reserved2
  have sameFinal : final2 = final := (ConstructionResult.ok.inj (cancelled2.symm.trans cancelled)).2
  subst final2
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout owner ty request origin knownCount before allocated id
    world.ownership.source.structural.1.1.1 created
  have fresh := newDestination_fresh_id config.layout owner ty request origin knownCount before allocated id created
  let target := { before with construction := final }
  have original := world.backing.observations config.layout before live
  have rootFrame : RootedBackingPrefixFrame before target live (storageExtent before) := by
    refine ⟨?_, ?_, ?_⟩
    · intro root retained; rfl
    · intro root retained; rfl
    · intro root retained value found stored occurrence
      have backed := (world.backing.values root retained value found).occurrence_backing config.layout before value stored occurrence
      obtain ⟨originalStorage, run, present, sampled, interval⟩ := backed.sampled config.layout before stored
      have finalStorage := storage stored.storage originalStorage present
      refine ⟨⟨originalStorage, originalStorage, present, finalStorage, ?_, rfl⟩, ?_⟩
      · simp only [storageExtent, present, Option.map_some, Option.getD_some]
        exact ⟨Nat.le_refl _, Nat.le_refl _, rfl⟩
      · intro destination named
        have inside := backed.named_bound config.layout before stored destination named
        have earlier : destination < id := by simpa only [fresh] using inside
        exact (rows destination earlier).trans (frame.lookup destination inside)
  refine ⟨reserved, final, reserve, cancelled, ?_⟩
  have preserved := original.prefix_frame config.layout before target live (storageExtent before) rootFrame
  have sameTarget : { allocated with construction := final } = target := by
    rw [frame.outer]
  rw [sameTarget]
  exact preserved

#print axioms allocated_receiver_cancel_rooted

end Goose.Proofs.ConstructionAcceptedExecution
