import Goose.Proofs.ConstructionAcceptedDestinationOwnership

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem newDestination_acceptedWorld (config : EvalConfig) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (knownCount : Option Nat) (initialized : Nat) (before after : ExecutionState) (id : Nat)
    (ambient : OwnershipAmbient) (types : RootTypes) (liveRoots : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (valid : AcceptedWorld config initialized before ambient types liveRoots regions pending)
    (executed : newDestination config.layout owner ty request origin none knownCount before = .ok id after) :
    AcceptedWorld config initialized after ambient types liveRoots
      (freshReceivingRegion before id :: regions) pending := by
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout owner ty request origin knownCount before after id
    valid.ownership.source.structural.1.1.1 executed
  have objects := congrArg ExecutionState.objects frame.outer
  have acts := congrArg ExecutionState.nextAct frame.outer
  have scopes := congrArg ExecutionState.nextScope frame.outer
  refine ⟨newDestination_ownershipContext config.layout owner ty request origin knownCount before after id ambient valid.ownership executed,
    ?_, valid.globalLive, valid.globalTypes, valid.layouts, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨valid.globals.1, ?_⟩
    intro global bound
    obtain ⟨descriptor, value, present, found, represented⟩ := valid.globals.2 global bound
    exact ⟨descriptor, value, present, by rw [objects]; exact found, represented⟩
  · intro act scope varId ty declared
    simpa only [acts, scopes] using valid.typeFrontier act scope varId ty declared
  · intro root ty value declared found
    rw [objects] at found
    exact valid.heap root ty value declared found
  · simpa only [executed, Goose.Proofs.Exit.stepState] using
      valid.backing.newDestination_frame config.layout owner ty request origin knownCount before liveRoots
  · intro region member
    rcases List.mem_cons.mp member with same | member
    · subst region
      exact newDestination_receivingProtection config.layout owner ty request origin knownCount before after id liveRoots valid.backing executed
    · exact frame.protection config.layout liveRoots region (valid.protections region member)
  · intro carrierFrame member
    obtain ⟨ready, backed⟩ := valid.carriers carrierFrame member
    exact ⟨frame.carriers_ready carrierFrame.channels carrierFrame.carriers ready,
      fun carrier present => frame.carrier_backing config.layout carrier (backed carrier present)⟩

#print axioms newDestination_acceptedWorld

end Goose.Proofs.ConstructionAcceptedExecution
