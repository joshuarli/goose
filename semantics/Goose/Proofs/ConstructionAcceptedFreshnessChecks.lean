import Goose.Proofs.ConstructionAcceptedFreshness
import Goose.Proofs.ConstructionAcceptedDestinationWorld
import Goose.Proofs.ConstructionAcceptedStaticBytes

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

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

theorem staticBytes_after_newDestination (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (owner : Goose.Core.ActId) (ty : Ty) (request : Goose.Core.ConstructionRequest)
    (origin : Goose.Core.OriginId) (knownCount : Option Nat) (before allocated : ExecutionState)
    (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes) (liveRoots : Goose.Core.RootInst → Prop)
    (environment : RuntimeActivation) (interpretation : RootInterpretation) (bytes : List UInt8) (bytesOrigin : Nat)
    (world : AcceptedWorld config initialized before ambient types liveRoots [] [])
    (allocatedDestination : newDestination config.layout owner ty request origin none knownCount before = .ok id allocated)
    (globals : interpretation.globalCount = config.module.globals.size) :
    ∃ after nextTypes root,
      evalValue (fuel + 1) config environment (.bytes (.slice .readOnly (.int .u8)) bytes bytesOrigin) allocated =
        .ok (.slice ⟨root, []⟩ 0 bytes.length) after ∧
      RootTypesExtend types nextTypes ∧
      AcceptedWorld config initialized after ambient nextTypes (fun other => other = root ∨ liveRoots other)
        [freshReceivingRegion before id] [] ∧
      AcceptedValue config.layout nextTypes interpretation after (.slice .readOnly (.int .u8)) [.static]
        (.slice ⟨root, []⟩ 0 bytes.length) := by
  have allocatedWorld := newDestination_acceptedWorld config owner ty request origin knownCount initialized
    before allocated id ambient types liveRoots [] [] world allocatedDestination
  exact evalValue_staticBytes_world fuel config initialized environment interpretation allocated ambient types liveRoots
    bytes bytesOrigin allocatedWorld globals

#print axioms freshScope_after_newDestination
#print axioms staticBytes_after_newDestination

end Goose.Proofs.ConstructionAcceptedExecution
