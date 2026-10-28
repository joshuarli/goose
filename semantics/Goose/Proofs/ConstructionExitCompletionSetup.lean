import Goose.Proofs.ConstructionExitCompletionHistory

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionExecutionOwnership

def completionPlanAction (channels : List Channel) (origin : OriginId) : EvalM (List (Channel × Option Nat)) :=
  channels.mapM fun channel => match channel with
  | .construct incoming => do
      let token ← liftConstruction origin (waitExitDestination incoming)
      pure (Channel.completion token, some token)
  | .register ty => pure (Channel.register ty, none)
  | .completion _ => fault .flow

theorem completion_setup_plan_equation (channels : List Channel) (origin : OriginId) :
    ownershipCompletionSetupAt channels origin = (do
      let planned ← completionPlanAction channels origin
      pure (planned.map Prod.fst, planned.filterMap Prod.snd)) := rfl

theorem completion_setup_plan_success (channels : List Channel) (origin : OriginId)
    (before after : ExecutionState) (planned : List Channel) (tokens : List Nat)
    (executed : ownershipCompletionSetupAt channels origin before = .ok (planned, tokens) after) :
    ∃ entries, completionPlanAction channels origin before = .ok entries after ∧
      entries.map Prod.fst = planned ∧ entries.filterMap Prod.snd = tokens := by
  rw [completion_setup_plan_equation] at executed
  cases plan : completionPlanAction channels origin before with
  | stop reason state | escape target carriers state | jump target kind state =>
    simp only [bind, plan] at executed
    cases executed
  | ok entries state =>
    simp only [bind, plan, pure, ExecutionStep.ok.injEq, Prod.mk.injEq] at executed
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := executed
    exact ⟨entries, rfl, rfl, rfl⟩

#print axioms completion_setup_plan_equation
#print axioms completion_setup_plan_success

theorem completion_setup_reference_history (channels : List Channel) (origin : OriginId)
    (before after : ExecutionState) (planned : List Channel) (tokens : List Nat)
    (ambient : OwnershipAmbient) (carriers : List Carrier) (activation : RuntimeActivation)
    (valid : ReservationReferencesBounded before.construction ambient)
    (executed : ownershipCompletionSetupAt channels origin before = .ok (planned, tokens) after)
    (activationChannels : activation.channels = planned) :
    ReservationReferencesBounded after.construction
      (.callChannels activation carriers :: .completionChannels tokens channels [] :: ambient) := by
  obtain ⟨entries, plan, channelEq, tokenEq⟩ := completion_setup_plan_success channels origin before after planned tokens executed
  let targetAction : EvalM (List (Channel × Option Nat)) := channels.mapM fun channel =>
    completion_plan_reference_bounds.match_1 (fun _ => EvalM (Channel × Option Nat)) channel
      (fun incoming => do
        let token ← liftConstruction origin (waitExitDestination incoming)
        pure (.completion token, some token))
      (fun ty => pure (.register ty, none))
      (fun _ => fault .flow)
  have sameAction : completionPlanAction channels origin = targetAction := by
    unfold completionPlanAction targetAction
    congr 1
  have bounded := completion_plan_reference_history channels origin before after entries ambient carriers activation valid
    (by change targetAction before = .ok entries after; rw [← sameAction]; exact plan)
    (by simpa only [channelEq] using activationChannels)
  simpa only [channelEq, tokenEq] using bounded

#print axioms completion_setup_reference_history

theorem completion_setup_history_and_coverage (channels : List Channel) (origin : OriginId)
    (before after : ExecutionState) (planned : List Channel) (tokens : List Nat)
    (ambient : OwnershipAmbient) (carriers : List Carrier) (activation : RuntimeActivation)
    (pending : List PendingCarrierFrame)
    (valid : ReservationReferencesBounded before.construction ambient)
    (coverage : ∀ id, .completed id ∈ ambient.retained → ∃ frame ∈ pending, .completed id ∈ frame.carriers)
    (executed : ownershipCompletionSetupAt channels origin before = .ok (planned, tokens) after)
    (activationChannels : activation.channels = planned) :
    ReservationReferencesBounded after.construction
      (.callChannels activation carriers :: .completionChannels tokens channels [] :: ambient) ∧
    (∀ id, .completed id ∈ OwnershipAmbient.retained
        (.callChannels activation carriers :: .completionChannels tokens channels [] :: ambient) →
      ∃ frame ∈ ({ channels := planned, carriers := carriers } :: pending), .completed id ∈ frame.carriers) := by
  refine ⟨completion_setup_reference_history channels origin before after planned tokens ambient carriers activation valid executed activationChannels, ?_⟩
  intro id member
  simp only [OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers, List.nil_append,
    List.mem_append] at member
  rcases member with direct | old
  · exact ⟨{ channels := planned, carriers := carriers }, by simp, direct⟩
  · obtain ⟨frame, present, kept⟩ := coverage id old
    exact ⟨frame, List.mem_cons_of_mem _ present, kept⟩

#print axioms completion_setup_history_and_coverage

end Goose.Proofs.ConstructionAcceptedExecution
