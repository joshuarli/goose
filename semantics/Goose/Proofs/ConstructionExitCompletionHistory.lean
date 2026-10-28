import Goose.Proofs.ConstructionExitReservationRooted
import Goose.Proofs.OwnershipAmbientContinuations
import Goose.Proofs.ConstructionExitReservationHistoryFrames

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionExecutionOwnership

theorem completion_plan_reference_bounds (channels : List Channel) (origin : OriginId)
    (before after : ExecutionState) (planned : List (Channel × Option Nat))
    (executed : ((channels.mapM fun (channel : Channel) => match channel with
      | .construct incoming => do
          let token ← liftConstruction origin (waitExitDestination incoming)
          pure (Channel.completion token, some token)
      | .register ty => pure (Channel.register ty, none)
      | .completion _ => fault .flow) : EvalM (List (Channel × Option Nat))) before = .ok planned after) :
    before.construction.exitReservations.size ≤ after.construction.exitReservations.size ∧
    (∀ token, .completion token ∈ planned.map Prod.fst → token < after.construction.exitReservations.size) ∧
    (∀ token ∈ planned.filterMap Prod.snd, token < after.construction.exitReservations.size) := by
  induction channels generalizing before planned with
  | nil =>
    simp only [List.mapM_nil, pure, ExecutionStep.ok.injEq] at executed
    obtain ⟨rfl, rfl⟩ := executed
    simp
  | cons channel rest ih =>
    cases channel with
    | completion named =>
      simp [List.mapM_cons, fault, EvalM.stop, bind] at executed
    | register ty =>
      simp only [List.mapM_cons, pure, bind] at executed
      cases tail : ((rest.mapM fun (channel : Channel) => match channel with
        | .construct incoming => do
            let token ← liftConstruction origin (waitExitDestination incoming)
            pure (Channel.completion token, some token)
        | .register ty => pure (Channel.register ty, none)
        | .completion _ => fault .flow) : EvalM (List (Channel × Option Nat))) before with
      | stop reason state | escape target carriers state | jump target kind state =>
        have normalized := tail
        simp only [bind, pure] at normalized
        rw [normalized] at executed
        cases executed
      | ok result state =>
        have normalized := tail
        simp only [bind, pure] at normalized
        rw [normalized] at executed
        simp only [ExecutionStep.ok.injEq] at executed
        obtain ⟨rfl, rfl⟩ := executed
        obtain ⟨size, channelBounds, tokenBounds⟩ := ih before result tail
        refine ⟨size, ?_, ?_⟩
        · intro token member
          simp only [List.map_cons, List.mem_cons, reduceCtorEq, false_or] at member
          exact channelBounds token member
        · simpa only [List.filterMap_cons, Option.isSome_none, List.filterMap_nil, List.mem_filterMap] using tokenBounds
    | construct incoming =>
      let token := before.construction.exitReservations.size
      let next := { before with construction := { before.construction with
        exitReservations := before.construction.exitReservations.push (.waiting incoming) } }
      have waiting : waitExitDestination incoming before.construction = .ok token next.construction := by
        simp [token, next, waitExitDestination, ConstructionM.get, ConstructionM.set, bind, pure]
      simp only [List.mapM_cons, liftConstruction, waiting, bind, pure] at executed
      cases tail : ((rest.mapM fun (channel : Channel) => match channel with
        | .construct incoming => do
            let token ← liftConstruction origin (waitExitDestination incoming)
            pure (Channel.completion token, some token)
        | .register ty => pure (Channel.register ty, none)
        | .completion _ => fault .flow) : EvalM (List (Channel × Option Nat))) next with
      | stop reason state | escape target carriers state | jump target kind state =>
        have normalized := tail
        simp only [liftConstruction, bind, pure] at normalized
        rw [normalized] at executed
        cases executed
      | ok result state =>
        have normalized := tail
        simp only [liftConstruction, bind, pure] at normalized
        rw [normalized] at executed
        simp only [ExecutionStep.ok.injEq] at executed
        obtain ⟨rfl, rfl⟩ := executed
        obtain ⟨size, channelBounds, tokenBounds⟩ := ih next result tail
        have freshBound : token < state.construction.exitReservations.size := by
          have grown : token < next.construction.exitReservations.size := by simp [token, next]
          exact Nat.lt_of_lt_of_le grown size
        refine ⟨?_, ?_, ?_⟩
        · exact Nat.le_trans (by simp [next]) size
        · intro id member
          simp only [List.map_cons, List.mem_cons, Channel.completion.injEq] at member
          rcases member with rfl | member
          · exact freshBound
          · exact channelBounds id member
        · intro id member
          simp only [List.filterMap_cons, List.mem_cons, Option.isSome_some] at member
          rcases member with rfl | member
          · exact freshBound
          · exact tokenBounds id member

#print axioms completion_plan_reference_bounds

theorem completion_plan_reference_history (channels : List Channel) (origin : OriginId)
    (before after : ExecutionState) (planned : List (Channel × Option Nat))
    (ambient : OwnershipAmbient) (carriers : List Carrier) (activation : RuntimeActivation)
    (valid : ReservationReferencesBounded before.construction ambient)
    (executed : ((channels.mapM fun (channel : Channel) => match channel with
      | .construct incoming => do
          let token ← liftConstruction origin (waitExitDestination incoming)
          pure (Channel.completion token, some token)
      | .register ty => pure (Channel.register ty, none)
      | .completion _ => fault .flow) : EvalM (List (Channel × Option Nat))) before = .ok planned after)
    (activationChannels : activation.channels = planned.map Prod.fst) :
    ReservationReferencesBounded after.construction
      (.callChannels activation carriers :: .completionChannels (planned.filterMap Prod.snd) channels [] :: ambient) := by
  obtain ⟨size, channelBounds, tokenBounds⟩ := completion_plan_reference_bounds channels origin before after planned executed
  have old := reservationReferencesBounded_mono before.construction after.construction ambient size valid
  intro frame member
  simp only [List.mem_cons] at member
  rcases member with same | same | member
  · subst frame
    refine ⟨by simp [OwnershipAmbientFrame.tickets], ?_⟩
    intro token found
    rw [activationChannels] at found
    exact channelBounds token found
  · subst frame
    refine ⟨?_, trivial⟩
    intro token found
    exact tokenBounds token found
  · exact old frame member

#print axioms completion_plan_reference_history



end Goose.Proofs.ConstructionAcceptedExecution
