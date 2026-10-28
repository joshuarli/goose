import Goose.Proofs.ConstructionExitReleaseWorld

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem ready_completion_ticket_present (state : ExecutionState) (channels : List Channel) (carriers : List Carrier)
    (ready : CarriersLandingReady state channels carriers) (token : Nat) (member : .completion token ∈ channels) :
    ∃ reservation, state.construction.exitReservations[token]? = some reservation := by
  induction channels generalizing carriers with
  | nil => cases member
  | cons channel rest ih =>
    cases carriers with
    | nil => have lengths := ready.lengths; simp at lengths
    | cons carrier tail =>
      have head : CarrierLandingReady state channel carrier := ready.pairs _ _ (by simp)
      have tailReady : CarriersLandingReady state rest tail := by
        refine ⟨?_, ?_⟩
        · simpa only [List.length_cons, Nat.succ.injEq] using ready.lengths
        · intro next item pair
          apply ready.pairs
          simp only [List.zip_cons_cons, List.mem_cons]
          exact Or.inr pair
      rcases List.mem_cons.mp member with equal | tailMember
      · subst channel
        cases head with
        | completion token incoming selected source role snapshot ticket sourceReady => exact ⟨_, ticket⟩
        | pendingNamed token incoming selected snapshot ticket => exact ⟨_, ticket⟩
      · exact ih tail tailReady tailMember

theorem acceptedWorld_fresh_pending_separate (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state ambient types live regions pending) :
    ∀ frame ∈ pending, .completion state.construction.exitReservations.size ∉ frame.channels := by
  intro frame member present
  obtain ⟨reservation, found⟩ := ready_completion_ticket_present state frame.channels frame.carriers
    (world.carriers frame member).1 state.construction.exitReservations.size present
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  omega

theorem acceptedWorld_new_tickets_pending_separate (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame) (tokens : List Nat)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (fresh : ∀ token ∈ tokens, state.construction.exitReservations.size ≤ token) :
    ∀ token ∈ tokens, ∀ frame ∈ pending, .completion token ∉ frame.channels := by
  intro token tokenMember frame member present
  obtain ⟨reservation, found⟩ := ready_completion_ticket_present state frame.channels frame.carriers
    (world.carriers frame member).1 token present
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have outside := fresh token tokenMember
  omega

theorem exit_cleanup_world_with_fresh_history (config : EvalConfig) (initialized : Nat)
    (before state : ExecutionState) (token incoming selected : Nat) (snapshot : PendingDestination)
    (channels : List Channel) (carriers : List Carrier) (oldAmbient outer : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame) (origin : OriginId)
    (oldWorld : AcceptedWorld config initialized before oldAmbient types live regions pending)
    (fresh : token = before.construction.exitReservations.size)
    (ticket : state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (world : AcceptedWorld config initialized state (.exitChannels [token] channels carriers :: outer) types live regions pending) :
    ∃ cleaned, exitChannelCleanupBorrowed origin [] [token] false carriers state = .ok () cleaned ∧
      AcceptedWorld config initialized cleaned (.returned carriers :: outer) types live regions pending := by
  apply exit_cleanup_accepted_world config initialized state token incoming selected snapshot channels carriers outer types live regions pending origin ticket world
  simpa only [fresh] using acceptedWorld_fresh_pending_separate config initialized before oldAmbient types live regions pending oldWorld

#print axioms acceptedWorld_new_tickets_pending_separate
#print axioms acceptedWorld_fresh_pending_separate
#print axioms exit_cleanup_world_with_fresh_history

end Goose.Proofs.ConstructionAcceptedExecution
