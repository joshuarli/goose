import Goose.Proofs.ConstructionAcceptedByteAllocationOutcome
import Goose.Proofs.ConstructionAcceptedFreshByteCompletion

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

theorem allocate_then_complete_byte_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (caller producer : RuntimeActivation) (bytes : List UInt8)
    (allocationOrigin origin : OriginId) (knownCount : Option Nat) (before : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (world : AcceptedWorld config frame.initialized before ambient types live [] [])
    (source : AcceptedFrame config accepted frame before types)
    (history : ReservationReferencesBounded before.construction ambient)
    (fits : bytes.length < 2 ^ 32) (noRetained : completedCarrierIds ambient.retained = []) :
    let outcome := (do
      let id ← newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount
      withCompletionChannels [.construct id] origin
        (fun channels => evalProduce fuel config producer channels (.bytes (.varr (.int .u8)) bytes origin))) before
    match outcome with
    | .stop _ after => ∃ nextAmbient nextRegions,
        AcceptedWorld config frame.initialized after nextAmbient types live nextRegions []
    | .ok carriers after => ∃ id, carriers = [.completed id] ∧
        AcceptedWorld config frame.initialized after (.returned carriers :: ambient) types live [freshReceivingRegion before id]
          [⟨[.construct id], carriers⟩]
    | _ => False := by
  have allocation := newDestination_byteOwner_world_outcome config accepted frame caller.act allocationOrigin knownCount
    before ambient types live [] [] world source
  cases created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before with
  | escape address carriers after | jump target kind after => simp [created] at allocation
  | stop reason after =>
    simp only [created] at allocation
    simp only [created, bind]
    exact ⟨ambient, [], allocation.1⟩
  | ok id allocated =>
    have completed := fresh_byteCompletion_allFuel fuel config frame.initialized caller producer bytes allocationOrigin origin knownCount
      before allocated id ambient types live world history fits noRetained created
    cases finished : withCompletionChannels [.construct id] origin
        (fun channels => evalProduce fuel config producer channels (.bytes (.varr (.int .u8)) bytes origin)) allocated with
    | escape address carriers after | jump target kind after => simp [finished] at completed
    | stop reason after =>
      simp only [finished, Goose.Proofs.Exit.stepState] at completed
      obtain ⟨carriers, pending, finalWorld, sameCarriers, samePending⟩ := completed
      subst carriers
      subst pending
      simp only [created, bind, finished]
      exact ⟨.returned [] :: ambient, [freshReceivingRegion before id], finalWorld⟩
    | ok carriers after =>
      simp only [finished, Goose.Proofs.Exit.stepState] at completed
      obtain ⟨retained, pending, finalWorld, sameCarriers, sameRetained, samePending⟩ := completed
      subst retained
      subst pending
      simp only [created, bind, finished]
      exact ⟨id, sameCarriers, by simpa only [sameCarriers] using finalWorld⟩

#print axioms allocate_then_complete_byte_world
end Goose.Proofs.ConstructionAcceptedExecution
