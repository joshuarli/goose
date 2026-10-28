import Goose.Proofs.ConstructionExitCompletionSetup
import Goose.Proofs.ConstructionExitByteBacking
import Goose.Proofs.ExitExecutionChecks

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem accepted_byte_receiver_produced_frame (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (bytes : List UInt8) (origin : OriginId) (id count : Nat)
    (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (openBacking : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : openBacking.destination.layout = .packed)
    (request : openBacking.destination.capability.request = .value)
    (receiver : openBacking.destination.use = .receiver)
    (fits : count + bytes.length < 2 ^ 32)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after)
    (coverage : ∀ old, .completed old ∈ ambient.retained → ∃ frame ∈ pending, .completed old ∈ frame.carriers) :
    let frame : PendingCarrierFrame := ⟨[.construct id], [.completed id]⟩
    CarriersLandingReady after frame.channels frame.carriers ∧
      (∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout after carrier) ∧
      landCarriersInto origin frame.channels frame.carriers after = .ok () after ∧
      (∀ retained, .completed retained ∈ OwnershipAmbient.retained (.returned [.completed id] :: ambient) →
        ∃ prior ∈ frame :: pending, .completed retained ∈ prior.carriers) := by
  obtain ⟨backed, ⟨ready⟩, landed⟩ := accepted_byte_receiver_landing_ready fuel config initialized environment bytes origin id count
    before after ambient types live regions pending world openBacking packed request receiver fits current executed
  refine ⟨⟨rfl, ?_⟩, ?_, landed, ?_⟩
  · intro channel carrier member
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    exact .construct id id ready
  · intro carrier member
    simp only [List.mem_singleton] at member
    subst carrier
    exact backed
  · intro retained member
    simp only [OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers,
      List.mem_append, List.mem_singleton, Carrier.completed.injEq] at member
    rcases member with rfl | prior
    · exact ⟨⟨[.construct retained], [.completed retained]⟩, by simp, by simp⟩
    · obtain ⟨old, present, kept⟩ := coverage retained prior
      exact ⟨old, List.mem_cons_of_mem _ present, kept⟩

#print axioms accepted_byte_receiver_produced_frame

theorem validated_nonempty_nested_return_witness :
    validate Goose.Proofs.ExitExecutionChecks.recursiveDestinations = .ok () ∧
    Goose.Proofs.ExitExecutionChecks.timeoutActivations
      (runModule 28 ⟨.release, Goose.Proofs.ExitExecutionChecks.recursiveDestinations⟩ .initial) = some ([3, 2, 1, 0], 4) ∧
    Goose.Proofs.ExitExecutionChecks.selectedActivation
      (targetActivation ⟨.release, Goose.Proofs.ExitExecutionChecks.recursiveDestinations⟩ 0
        (Goose.Proofs.Exit.stepState (runModule 28 ⟨.release, Goose.Proofs.ExitExecutionChecks.recursiveDestinations⟩ .initial))) = some 2 ∧
    Goose.Proofs.ExitExecutionChecks.returnedObservation (eval 200 .release Goose.Proofs.ExitExecutionChecks.recursiveDestinations) =
      some ([66, 10, 65, 10], [.begin 0, .begin 1, .write 1 0, .publish 1, .write 0 0, .publish 0]) := by
  have validated := Goose.Proofs.ExitExecutionChecks.recursiveDestinations_validated
  have exactValidation : validate Goose.Proofs.ExitExecutionChecks.recursiveDestinations = .ok () := by
    cases result : validate Goose.Proofs.ExitExecutionChecks.recursiveDestinations with
    | ok value => cases value; rfl
    | error reason => simp [Goose.Proofs.ExitExecutionChecks.accepts, result] at validated
  exact ⟨exactValidation, Goose.Proofs.ExitExecutionChecks.recursive_live_activations,
    Goose.Proofs.ExitExecutionChecks.recursive_live_nearest_target,
    Goose.Proofs.ExitExecutionChecks.recursiveDestinations_execution⟩

#print axioms validated_nonempty_nested_return_witness

end Goose.Proofs.ConstructionAcceptedExecution
