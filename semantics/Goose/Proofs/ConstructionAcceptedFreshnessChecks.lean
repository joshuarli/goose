import Goose.Proofs.ConstructionAcceptedFreshness
import Goose.Proofs.ConstructionAcceptedDestinationWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem freshScope_after_newDestination (config : EvalConfig) (initialized : Nat)
    (owner : Goose.Core.ActId) (ty : Ty) (request : Goose.Core.ConstructionRequest)
    (origin : Goose.Core.OriginId) (knownCount : Option Nat) (before allocated : ExecutionState)
    (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes) (liveRoots : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config initialized before ambient types liveRoots [] [])
    (allocatedDestination : newDestination config.layout owner ty request origin none knownCount before = .ok id allocated) :
    ∃ afterScope, freshScope allocated = .ok allocated.nextScope afterScope ∧
      AcceptedWorld config initialized afterScope ambient types liveRoots [freshReceivingRegion before id] [] := by
  have allocatedWorld := newDestination_acceptedWorld config owner ty request origin knownCount initialized
    before allocated id ambient types liveRoots [] [] world allocatedDestination
  exact ⟨_, (freshScope_acceptedWorld config initialized allocated ambient types liveRoots allocatedWorld).1,
    (freshScope_acceptedWorld config initialized allocated ambient types liveRoots allocatedWorld).2⟩

#print axioms freshScope_after_newDestination

end Goose.Proofs.ConstructionAcceptedExecution
