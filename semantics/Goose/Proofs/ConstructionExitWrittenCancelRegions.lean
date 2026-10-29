import Goose.Proofs.ConstructionExitWrittenCancelRoots

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem allocated_byte_write_cancel_regions (config : EvalConfig) (initialized : Nat) (owner : ActId)
    (origin : OriginId) (knownCount : Option Nat) (byte : UInt8)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout owner (.varr (.int .u8)) .value origin none knownCount before = .ok id allocated) :
    ∃ reserved written final,
      reserveExitDestination id .newValue allocated.construction = .ok (allocated.construction.exitReservations.size, id) reserved ∧
      writeElement id ⟨#[byte]⟩ reserved = .ok () written ∧
      (do
        cancelExitReservation allocated.construction.exitReservations.size []
        releaseExitReservation allocated.construction.exitReservations.size) written = .ok () final ∧
      ∀ region ∈ regions, ReceivingProtection config.layout { allocated with construction := final } live region := by
  obtain ⟨reserved, written, final, reserve, write, cancel, rooted, oldRow, storage⟩ :=
    allocated_byte_write_cancel_frame config initialized owner origin knownCount byte before allocated id ambient types live regions pending world created
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout owner (.varr (.int .u8)) .value origin knownCount before allocated id
    world.ownership.source.structural.1.1.1 created
  have objects : allocated.objects = before.objects := by
    simpa only using congrArg ExecutionState.objects frame.outer
  refine ⟨reserved, written, final, reserve, write, cancel, ?_⟩
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

#print axioms allocated_byte_write_cancel_regions

end Goose.Proofs.ConstructionAcceptedExecution
