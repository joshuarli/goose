import Goose.Proofs.ExitExecutionAcceptedLanding
import Goose.Proofs.ExitExecutionLandingMetadata

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionAcceptedExecution

theorem constructed_byte_finish_protects_reads (module : Goose.Construct.Module) (accepted : validate module = .ok ())
    (origin : OriginId) (before : ExecutionState) (ambient : OwnershipAmbient) (incoming source count : Nat)
    (receiver replacement : PendingDestination) (live : RootInst → Prop) (region : ReceivingRegion)
    (context : OwnershipExecutionContext before ambient)
    (backed : CarrierResultBacking (.ofModule module) before (.completed source))
    (ready : ReceivingCarrierLandingReady before incoming source)
    (protection : ReceivingProtection (.ofModule module) before live region)
    (receivingRegion : region.destination = ready.receiving)
    (sourceMutable : source ∈ region.mutableDestinations)
    (abandonedMutable : ∀ row ∈ protectedRows before.construction ready.receiving source,
      row.capability.id ∈ region.mutableDestinations)
    (parentMutable : ∀ parent, ready.receivingDestination.use = .child parent ∨
      ready.receivingDestination.use = .replacement parent → parent ∈ region.mutableDestinations)
    (resolved : destinationCurrent before.construction incoming = .ok incoming)
    (different : incoming ≠ source)
    (receiverPresent : before.construction.destinations[incoming]? = some receiver)
    (receiverRole : receiver.use = .receiver)
    (sourcePresent : before.construction.destinations[source]? = some replacement)
    (sourceBuilt : replacement.progress = .built count)
    (adaptation : replacement.adaptation = none)
    (physical : replacement.capability.layout = .varr (.int .u8))
    (logical : replacement.capability.logicalType = .varr (.int .u8)) :
    ∃ after, finishChannels (.ofModule module) [.construct incoming] [.varr (.int .u8)] [.completed source] origin before = .ok () after ∧
      after.construction.stdout = before.construction.stdout ∧
      ∀ (fuel : Nat) (location : Loc), live location.root → ¬ region.mutableRoots location.root →
        mapStepState (fun _ => ExecutionState.initial) (readLoc fuel (.ofModule module) location after) =
          mapStepState (fun _ => ExecutionState.initial) (readLoc fuel (.ofModule module) location before) := by
  obtain ⟨after, landed, _, _, _, _, stdout, observations⟩ :=
    landCarriersInto_construct_protected module accepted origin before ambient incoming source live region context backed ready
      protection receivingRegion sourceMutable abandonedMutable parentMutable
  obtain ⟨other, otherLanded, _, _, _, frame⟩ :=
    landCarriersInto_construct_completed (.ofModule module) origin before ambient incoming source context backed ready
  have same := landed.symm.trans otherLanded
  cases same
  obtain ⟨row, present, receiver, adapt, phys, logic, built⟩ :=
    frame.replacement_receiver_metadata before after incoming source count receiver replacement
      resolved different receiverPresent receiverRole sourcePresent sourceBuilt
  have finished := byte_receiver_finishChannel (.ofModule module) origin after source count row present built receiver
    (adapt.trans adaptation) (phys.trans physical) (logic.trans logical)
  refine ⟨after, ?_, stdout, observations⟩
  simp only [finishChannels, landed, List.length_cons, List.length_nil, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons,
    List.forIn_nil, bind, pure, finished]

#print axioms constructed_byte_finish_protects_reads

end Goose.Proofs.ExitExecution
