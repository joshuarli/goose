import Goose.Proofs.ConstructionAcceptedByteReturnAllFuel
import Goose.Proofs.ConstructionAcceptedByteAllocation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem fresh_byteCompletion_allFuel (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (caller producer : RuntimeActivation) (bytes : List UInt8) (allocationOrigin origin : OriginId)
    (knownCount : Option Nat) (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop)
    (world : AcceptedWorld config initialized before ambient types live [] [])
    (history : ReservationReferencesBounded before.construction ambient)
    (fits : bytes.length < 2 ^ 32)
    (noRetained : completedCarrierIds ambient.retained = [])
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none
      knownCount before = .ok id allocated) :
    let region := freshReceivingRegion before id
    let outcome := withCompletionChannels [.construct id] origin
      (fun channels => evalProduce fuel config producer channels (.bytes (.varr (.int .u8)) bytes origin)) allocated
    ∃ carriers pending,
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) (.returned carriers :: ambient) types live [region] pending ∧
      (match outcome with
      | .ok actual _ => actual = [.completed id] ∧ carriers = actual ∧ pending = [⟨[.construct id], [.completed id]⟩]
      | .stop .. => carriers = [] ∧ pending = []
      | _ => False) := by
  obtain ⟨ready⟩ := newDestination_initial_backing config.layout caller.act (.varr (.int .u8)) .value allocationOrigin
    knownCount before allocated id (.int .u8) rfl created
  obtain ⟨destination, found, packed, request, backing, receiver, adaptation⟩ :=
    newDestination_byteOwner_packed_value_with_adaptation config.layout caller.act allocationOrigin knownCount before allocated id created
  have same : destination = ready.destination := Option.some.inj (found.symm.trans ready.present)
  subst destination
  have allocatedWorld := newDestination_acceptedWorld config caller.act (.varr (.int .u8)) .value allocationOrigin knownCount
    initialized before allocated id ambient types live [] [] world created
  obtain ⟨freshFrame⟩ := newDestination_fresh_frame config.layout caller.act (.varr (.int .u8)) .value allocationOrigin knownCount
    before allocated id world.ownership.source.structural.1.1.1 created
  have allocatedHistory : ReservationReferencesBounded allocated.construction ambient := by
    simpa only [ReservationReferencesBounded, freshFrame.tickets] using history
  have current := newDestination_current_self config initialized caller.act (.varr (.int .u8)) .value allocationOrigin
    knownCount before allocated id ambient types live [] [] world created
  obtain ⟨freshRow, freshFound, freshStorage, afterSize⟩ :=
    newDestination_success_fresh config.layout caller.act (.varr (.int .u8)) .value allocationOrigin knownCount before allocated id created
  have sameRow : freshRow = ready.destination := Option.some.inj (freshFound.symm.trans ready.present)
  have extent : storageExtent before ready.destination.storage = 0 := by
    have bound : before.construction.storage.size ≤ ready.destination.storage := by simpa only [sameRow] using afterSize
    simp [storageExtent, Array.getElem?_eq_none_iff.mpr bound]
  have mutable : ∀ region ∈ [freshReceivingRegion before id], id ∈ region.mutableDestinations := by
    intro region member
    simp only [List.mem_singleton] at member
    subst region
    simp [freshReceivingRegion]
  have cutoff : ∀ region ∈ [freshReceivingRegion before id],
      region.limit ready.destination.storage ≤ ready.destination.capability.start := by
    intro region member
    simp only [List.mem_singleton] at member
    subst region
    simp [freshReceivingRegion, extent]
  have covered : ∀ root, live root → ∃ region ∈ [freshReceivingRegion before id], ¬ region.mutableRoots root := by
    intro root active
    exact ⟨freshReceivingRegion before id, by simp, by simp [freshReceivingRegion]⟩
  exact withCompletion_byteReceiver_allFuel fuel config initialized producer id bytes origin allocated ambient types live
    [freshReceivingRegion before id] allocatedWorld allocatedHistory noRetained ready packed adaptation receiver request current fits mutable cutoff covered

#print axioms fresh_byteCompletion_allFuel
end Goose.Proofs.ConstructionAcceptedExecution
