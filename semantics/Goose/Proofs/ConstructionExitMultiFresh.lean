import Goose.Proofs.ConstructionExitFreshSeparation
import Goose.Proofs.ExitExecutionPathContext

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem exitChannelReservationTokens_frontier (first : Nat) (state : ExecutionState) :
    ∀ token ∈ exitChannelReservationTokens first state,
      first ≤ token ∧ token < state.construction.exitReservations.size := by
  intro token member
  simp only [exitChannelReservationTokens, List.mem_map, List.mem_range] at member
  obtain ⟨index, inside, equal⟩ := member
  subst token
  constructor
  · exact Nat.le_add_right first index
  · have add := Nat.add_lt_add_left inside first
    have bound := Nat.add_sub_of_le (show first ≤ state.construction.exitReservations.size by omega)
    simpa only [bound] using add

theorem exitChannelReservationTokens_pending_separate (config : EvalConfig) (initialized : Nat)
    (before prepared : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending) :
    ∀ token ∈ exitChannelReservationTokens before.construction.exitReservations.size prepared,
      ∀ frame ∈ pending, .completion token ∉ frame.channels := by
  apply acceptedWorld_new_tickets_pending_separate config initialized before ambient types live regions pending _ world
  intro token member
  exact (exitChannelReservationTokens_frontier before.construction.exitReservations.size prepared token member).1

theorem reached_exit_channels_pending_separate (rootFuel fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (source target : RuntimeActivation) (targetId : Nat) (operands : List Expr) (origin : Goose.Core.OriginId)
    (before prepared : ExecutionState) (channels : List Channel) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reached : ExitReached rootFuel config (.statement (fuel + 1) source (.returnFrom targetId operands origin)) before)
    (selection : targetActivation config targetId before = .ok target before)
    (setup : exitChannels source target operands origin before = .ok channels prepared) :
    ExitReached rootFuel config (.operands fuel source channels operands) prepared ∧
    ∀ token ∈ exitChannelReservationTokens before.construction.exitReservations.size prepared,
      ∀ frame ∈ pending, .completion token ∉ frame.channels := by
  exact ⟨.call reached (.returnFromOperands fuel source target targetId operands origin before prepared channels selection setup),
    exitChannelReservationTokens_pending_separate config initialized before prepared ambient types live regions pending world⟩

#print axioms exitChannelReservationTokens_frontier
#print axioms exitChannelReservationTokens_pending_separate
#print axioms reached_exit_channels_pending_separate

end Goose.Proofs.ConstructionAcceptedExecution
