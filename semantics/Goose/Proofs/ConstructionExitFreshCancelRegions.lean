import Goose.Proofs.ConstructionExitFreshCancelRoots

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem allocated_receiver_cancel_regions (config : EvalConfig) (initialized : Nat) (owner : ActId)
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
      ∀ region ∈ regions, ReceivingProtection config.layout { allocated with construction := final } live region := by
  obtain ⟨reserved, final, reserve, cancelled, rows, tickets⟩ := allocated_receiver_direct_cancel config initialized owner
    ty element request origin knownCount before allocated id ambient types live regions pending world elementType created
  obtain ⟨reserved2, final2, reserve2, cancelled2, storage⟩ := allocated_receiver_cancel_old_storage config initialized owner
    ty element request origin knownCount before allocated id ambient types live regions pending world elementType created
  have sameReserved : reserved2 = reserved := (ConstructionResult.ok.inj (reserve2.symm.trans reserve)).2
  subst reserved2
  have sameFinal : final2 = final := (ConstructionResult.ok.inj (cancelled2.symm.trans cancelled)).2
  subst final2
  obtain ⟨reserved2, final2, reserve2, cancelled2, rooted⟩ := allocated_receiver_cancel_rooted config initialized owner
    ty element request origin knownCount before allocated id ambient types live regions pending world elementType created
  have sameReserved : reserved2 = reserved := (ConstructionResult.ok.inj (reserve2.symm.trans reserve)).2
  subst reserved2
  have sameFinal : final2 = final := (ConstructionResult.ok.inj (cancelled2.symm.trans cancelled)).2
  subst final2
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout owner ty request origin knownCount before allocated id
    world.ownership.source.structural.1.1.1 created
  have fresh := newDestination_fresh_id config.layout owner ty request origin knownCount before allocated id created
  have oldRow : ∀ index, index < before.construction.destinations.size →
      final.destinations[index]? = before.construction.destinations[index]? := by
    intro index inside
    exact (rows index (by simpa only [fresh] using inside)).trans (frame.lookup index inside)
  have objects : allocated.objects = before.objects := by
    simpa only using congrArg ExecutionState.objects frame.outer
  refine ⟨reserved, final, reserve, cancelled, ?_⟩
  intro region member
  have protection := world.protections region member
  obtain ⟨receiver, receiverFound⟩ := protection.present
  have receiverInside := (Array.getElem?_eq_some_iff.mp receiverFound).1
  have afterFound := (oldRow region.destination receiverInside).trans receiverFound
  refine ⟨⟨receiver, afterFound⟩, ?_, ?_, ?_, protection.authority, ?_, ?_⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro root kept value found
      exact rooted.backing.values root kept.1 value found
    · intro root kept stored found
      exact rooted.backing.identities root kept.1 stored found
    · intro root kept value found stored occurrence
      have initialFound : before.objects.lookup root = some value := by simpa only [objects] using found
      obtain ⟨oldStorage, run, fuel, finish, storedFound, sampled, measured, lower, upper⟩ :=
        (protection.observations.observations root kept value initialFound stored occurrence).observed
      have nextStorage := storage stored.storage oldStorage storedFound
      have backed := (protection.observations.backing.values root kept value initialFound).occurrence_backing
        config.layout before value stored occurrence
      have sameDest : ∀ namedId, stored.destination = some namedId →
          final.destinations[namedId]? = before.construction.destinations[namedId]? := by
        intro namedId named
        exact oldRow namedId (backed.named_bound config.layout before stored namedId named)
      refine ⟨oldStorage, run, fuel, finish, nextStorage, ?_, measured, lower, upper⟩
      exact sampledStored_storage_transport stored before { allocated with construction := final } oldStorage oldStorage run
        storedFound nextStorage rfl sameDest sampled
  · intro actual found
    have same : actual = receiver := Option.some.inj (found.symm.trans afterFound)
    subst actual
    exact protection.cutoff receiver receiverFound
  · intro actual found
    have same : actual = receiver := Option.some.inj (found.symm.trans afterFound)
    subst actual
    exact protection.landing receiver receiverFound
  · intro destination authority
    have inside := protection.authorityBound destination authority
    have existing : before.construction.destinations[destination]? = some before.construction.destinations[destination] :=
      Array.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩
    have afterExisting := (oldRow destination inside).trans existing
    exact (Array.getElem?_eq_some_iff.mp afterExisting).1
  · intro root active immutable value found stored occurrence namedId named
    apply protection.names root active immutable value ?_ stored occurrence namedId named
    simpa only [objects] using found

#print axioms allocated_receiver_cancel_regions

end Goose.Proofs.ConstructionAcceptedExecution
