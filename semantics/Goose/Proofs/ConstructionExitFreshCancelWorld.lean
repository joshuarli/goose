import Goose.Proofs.ConstructionExitFreshCancelSource
import Goose.Proofs.ConstructionExitReleasedAppendReceiving

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem allocated_receiver_cancel_world (config : EvalConfig) (initialized : Nat) (owner : ActId)
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
      AcceptedWorld config initialized { allocated with construction := final } ambient types live regions pending := by
  obtain ⟨reserved, final, reserve, cancel, lifecycle, successors, inactive, aliases, rawRoles, currentRoles,
    resumptions, savedStart, savedBacking, unsupported, authority, links, source, rooted, regionsSafe, frames⟩ :=
    allocated_receiver_cancel_source_roles config initialized owner ty element request origin knownCount before allocated id ambient types live
      regions pending world elementType created
  obtain ⟨otherReserved, otherFinal, otherReserve, otherCancel, ⟨frame⟩⟩ :=
    allocated_receiver_cancel_frame config initialized owner ty element request origin knownCount before allocated id ambient types live
      regions pending world elementType created
  have sameReserved : otherReserved = reserved := (ConstructionResult.ok.inj (otherReserve.symm.trans reserve)).2
  subst otherReserved
  have sameFinal : otherFinal = final := (ConstructionResult.ok.inj (otherCancel.symm.trans cancel)).2
  subst otherFinal
  have oldContext := released_ticket_append_context_unbounded before ambient world.ownership
  have context := frame.ownershipContext ambient oldContext source
  obtain ⟨allocation⟩ := newDestination_fresh_frame config.layout owner ty request origin knownCount before allocated id
    world.ownership.source.structural.1.1.1 created
  have objects : allocated.objects = before.objects := by simpa only using congrArg ExecutionState.objects allocation.outer
  have ordinals : allocated.objectOrdinals = before.objectOrdinals := by simpa only using congrArg ExecutionState.objectOrdinals allocation.outer
  have acts : allocated.nextAct = before.nextAct := by simpa only using congrArg ExecutionState.nextAct allocation.outer
  have scopes : allocated.nextScope = before.nextScope := by simpa only using congrArg ExecutionState.nextScope allocation.outer
  refine ⟨reserved, final, reserve, cancel, ?_⟩
  refine ⟨⟨context, ?_, world.globalTypes, world.layouts, ?_, ?_, ?_, ?_, ?_, rooted.backing, regionsSafe, frames⟩, world.globalLive⟩
  · refine ⟨world.globals.1, ?_⟩
    intro global bound
    obtain ⟨descriptor, value, present, found, represented⟩ := world.globals.2 global bound
    exact ⟨descriptor, value, present, by simpa only [objects] using found, represented⟩
  · intro act scope varId varTy declared
    simpa only [acts, scopes] using world.typeFrontier act scope varId varTy declared
  · intro global varTy declared outside
    simpa only [scopes] using world.syntheticFrontier global varTy declared outside
  · intro root varTy value declared found
    apply world.heap root varTy value declared
    simpa only [objects] using found
  · intro root value found
    apply world.objectsRegistered root value
    simpa only [objects] using found
  · intro root ordinal found
    apply world.ordinalsRegistered root ordinal
    simpa only [ordinals] using found

#print axioms allocated_receiver_cancel_world

end Goose.Proofs.ConstructionAcceptedExecution
