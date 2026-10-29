import Goose.Proofs.ConstructionExitEvaluationHistory
import Goose.Proofs.ConstructionAcceptedState

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem retained_destination_bounds (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (history : EvaluationHistoryCoverage state ambient pending) :
    ∀ id ∈ completedCarrierIds ambient.retained, id < state.construction.destinations.size := by
  intro id member
  have retained : .completed id ∈ ambient.retained := by
    simp only [completedCarrierIds, List.mem_filterMap] at member
    obtain ⟨carrier, present, equal⟩ := member
    cases carrier <;> simp_all
  obtain ⟨frame, frameMember, carrierMember⟩ := history.2 id retained
  have backed := (world.carriers frame frameMember).2 (.completed id) carrierMember
  cases backed with
  | completed id count row stored present built sampled backed =>
    exact (Array.getElem?_eq_some_iff.mp present).1

#print axioms retained_destination_bounds
end Goose.Proofs.ConstructionAcceptedExecution
