import Goose.Proofs.ConstructionExitEvaluationHistory

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem evaluationHistoryCoverage_push (state : ExecutionState) (ambient : OwnershipAmbient)
    (pending : List PendingCarrierFrame) (frame : OwnershipAmbientFrame) (channels : List Channel)
    (valid : EvaluationHistoryCoverage state ambient pending)
    (tickets : ∀ token ∈ frame.tickets, token < state.construction.exitReservations.size)
    (completionChannels : match frame with
      | .callChannels activation _ => ∀ token, .completion token ∈ activation.channels → token < state.construction.exitReservations.size
      | .breakTarget target _ => ∀ token, .completion token ∈ target.channels → token < state.construction.exitReservations.size
      | _ => True) :
    EvaluationHistoryCoverage state (frame :: ambient) ({ channels := channels, carriers := frame.carriers } :: pending) := by
  constructor
  · intro found member
    rcases List.mem_cons.mp member with same | old
    · subst found
      cases frame <;> exact ⟨tickets, completionChannels⟩
    · exact valid.1 found old
  · intro id retained
    simp only [OwnershipAmbient.retained, List.flatMap_cons, List.mem_append] at retained
    rcases retained with current | old
    · exact ⟨⟨channels, frame.carriers⟩, by simp, current⟩
    · obtain ⟨prior, present, covered⟩ := valid.2 id old
      exact ⟨prior, List.mem_cons_of_mem _ present, covered⟩

theorem evaluationHistoryCoverage_pop (state : ExecutionState) (ambient : OwnershipAmbient)
    (pending : List PendingCarrierFrame) (frame : OwnershipAmbientFrame)
    (valid : EvaluationHistoryCoverage state (frame :: ambient) pending) :
    EvaluationHistoryCoverage state ambient pending := by
  constructor
  · intro found member
    exact valid.1 found (List.mem_cons_of_mem frame member)
  · intro id retained
    apply valid.2 id
    simp only [OwnershipAmbient.retained, List.flatMap_cons, List.mem_append]
    exact Or.inr retained

theorem evaluationHistoryCoverage_returned (state : ExecutionState) (ambient : OwnershipAmbient)
    (pending : List PendingCarrierFrame) (channels : List Channel) (carriers : List Goose.Construct.Carrier)
    (valid : EvaluationHistoryCoverage state ambient pending) :
    EvaluationHistoryCoverage state (.returned carriers :: ambient) ({ channels := channels, carriers := carriers } :: pending) := by
  refine evaluationHistoryCoverage_push state ambient pending (.returned carriers) channels valid ?_ ?_
  · intro token member
    simp only [OwnershipAmbientFrame.tickets, List.not_mem_nil] at member
  · trivial

#print axioms evaluationHistoryCoverage_push
#print axioms evaluationHistoryCoverage_pop
#print axioms evaluationHistoryCoverage_returned

end Goose.Proofs.ConstructionAcceptedExecution
