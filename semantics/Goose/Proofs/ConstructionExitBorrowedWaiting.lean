import Goose.Proofs.ConstructionExitMixedCancellation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem borrowed_waiting_step (origin : OriginId) (carriers : List Carrier)
    (receipt : BorrowedWaitingExitReservation) (state : ExecutionState)
    (waiting : state.construction.exitReservations[receipt.token]? = some (.waiting receipt.incoming)) :
    borrowedExitChannelStep origin carriers receipt state = .ok (.yield PUnit.unit) state := by
  unfold borrowedExitChannelStep
  split
  · rfl
  · simp only [cancelExitReservation, ConstructionM.get, waiting, bind, pure, liftConstruction, EvalM.get]
    simp

theorem borrowed_waiting_loop (origin : OriginId) (carriers : List Carrier)
    (receipts : List BorrowedWaitingExitReservation) (state : ExecutionState)
    (waiting : ∀ receipt ∈ receipts, state.construction.exitReservations[receipt.token]? = some (.waiting receipt.incoming)) :
    ((forIn receipts PUnit.unit fun receipt _ => borrowedExitChannelStep origin carriers receipt) : EvalM PUnit) state =
      .ok PUnit.unit state := by
  induction receipts with
  | nil => rfl
  | cons receipt rest ih =>
    have first := borrowed_waiting_step origin carriers receipt state (waiting receipt (by simp))
    have remaining := ih (fun receipt member => waiting receipt (by simp [member]))
    simp only [List.forIn_cons, bind, first, remaining]

theorem borrowed_receipts_waiting_from_initial (activation : RuntimeActivation) (initial state : ExecutionState)
    (unchanged : ∀ token, token < initial.construction.exitReservations.size →
      state.construction.exitReservations[token]? = initial.construction.exitReservations[token]?) :
    ∀ receipt ∈ borrowedExitChannelReceipts activation initial,
      state.construction.exitReservations[receipt.token]? = some (.waiting receipt.incoming) := by
  intro receipt member
  obtain ⟨channel, channelMember, captured⟩ := List.mem_filterMap.mp member
  cases channel with
  | register ty => cases captured
  | construct id => cases captured
  | completion token =>
    have source := captureWaitingExitReservation_source token initial.construction receipt captured
    have inside := (Array.getElem?_eq_some_iff.mp source.2).1
    rw [source.1, unchanged token inside]
    exact source.2

#print axioms borrowed_receipts_waiting_from_initial

theorem actual_mixed_cancel_waiting_borrowed (layout : LayoutEnv) (origin : OriginId)
    (receipts : List BorrowedWaitingExitReservation) (tokens : List Nat)
    (state : ExecutionState) (carriers : List Carrier) (pending : List PendingCarrierFrame)
    (waiting : ∀ receipt ∈ receipts, state.construction.exitReservations[receipt.token]? = some (.waiting receipt.incoming))
    (distinct : tokens.Nodup)
    (tickets : ∀ token ∈ tokens, CancelableExitTicket state token (carriers.filterMap fun carrier =>
      match carrier with | Carrier.completed id => some id | _ => none))
    (frames : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking layout state carrier)
    (separate : ∀ token ∈ tokens, ∀ frame ∈ pending, .completion token ∉ frame.channels) :
    ∃ after, exitChannelCleanupBorrowed origin receipts tokens true carriers state = .ok () after ∧
      ∀ frame ∈ pending, CarriersLandingReady after frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking layout after carrier := by
  have reverseWaiting : ∀ receipt ∈ receipts.reverse, state.construction.exitReservations[receipt.token]? = some (.waiting receipt.incoming) := by simpa using waiting
  have borrowed := borrowed_waiting_loop origin carriers receipts.reverse state reverseWaiting
  obtain ⟨after, owned, result⟩ := actual_mixed_cancel_pending layout origin tokens state carriers pending distinct tickets frames separate
  have cleanup : exitChannelCleanupBorrowed origin receipts tokens true carriers state =
      exitChannelCleanupBorrowed origin [] tokens true carriers state := by
    simp only [exitChannelCleanupBorrowed, ↓reduceIte, List.reverse_nil, List.forIn_nil, bind, pure] at owned ⊢
    rw [borrowed]
  exact ⟨after, cleanup.trans owned, result⟩

theorem actual_exit_cancel_waiting_borrowed (config : EvalConfig) (initialized : Nat) (origin : OriginId)
    (activation : RuntimeActivation) (before prepared state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame) (carriers : List Carrier)
    (oldWorld : AcceptedWorld config initialized before ambient types live regions pending)
    (unchanged : ∀ token, token < before.construction.exitReservations.size →
      state.construction.exitReservations[token]? = before.construction.exitReservations[token]?)
    (tickets : ∀ token ∈ exitChannelReservationTokens before.construction.exitReservations.size prepared,
      CancelableExitTicket state token (carriers.filterMap fun carrier =>
        match carrier with | Carrier.completed id => some id | _ => none))
    (frames : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout state carrier) :
    ∃ after, exitChannelCleanupBorrowed origin (borrowedExitChannelReceipts activation before)
      (exitChannelReservationTokens before.construction.exitReservations.size prepared) true carriers state = .ok () after ∧
      ∀ frame ∈ pending, CarriersLandingReady after frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout after carrier := by
  exact actual_mixed_cancel_waiting_borrowed config.layout origin (borrowedExitChannelReceipts activation before) _ state carriers pending
    (borrowed_receipts_waiting_from_initial activation before state unchanged)
    (exitChannelReservationTokens_distinct before.construction.exitReservations.size prepared) tickets frames
    (exitChannelReservationTokens_pending_separate config initialized before prepared ambient types live regions pending oldWorld)

#print axioms actual_exit_cancel_waiting_borrowed
#print axioms borrowed_waiting_step
#print axioms borrowed_waiting_loop
#print axioms actual_mixed_cancel_waiting_borrowed

end Goose.Proofs.ConstructionAcceptedExecution
