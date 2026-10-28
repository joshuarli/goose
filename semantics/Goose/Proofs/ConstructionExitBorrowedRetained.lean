import Goose.Proofs.ConstructionExitBorrowedWaiting

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem borrowed_retained_step (origin : OriginId) (carriers : List Carrier)
    (receipt : BorrowedWaitingExitReservation) (state : ExecutionState)
    (retained : .pendingNamed receipt.token ∈ carriers) :
    borrowedExitChannelStep origin carriers receipt state = .ok (.yield PUnit.unit) state := by
  have present : carriers.any (fun carrier => match carrier with
      | .pendingNamed actual => actual == receipt.token | _ => false) = true := by
    induction carriers with
    | nil => cases retained
    | cons carrier rest ih =>
      rcases List.mem_cons.mp retained with equal | member
      · subst carrier
        simp
      · have tail := ih member
        cases carrier <;> simp_all
  unfold borrowedExitChannelStep
  split
  · rfl
  · rename_i absent
    exact False.elim (absent present)

theorem borrowed_retained_or_waiting_loop (origin : OriginId) (carriers : List Carrier)
    (receipts : List BorrowedWaitingExitReservation) (state : ExecutionState)
    (preserved : ∀ receipt ∈ receipts,
      .pendingNamed receipt.token ∈ carriers ∨
        state.construction.exitReservations[receipt.token]? = some (.waiting receipt.incoming)) :
    ((forIn receipts PUnit.unit fun receipt _ => borrowedExitChannelStep origin carriers receipt) : EvalM PUnit) state =
      .ok PUnit.unit state := by
  induction receipts with
  | nil => rfl
  | cons receipt rest ih =>
    have first : borrowedExitChannelStep origin carriers receipt state = .ok (.yield PUnit.unit) state := by
      rcases preserved receipt (by simp) with retained | waiting
      · exact borrowed_retained_step origin carriers receipt state retained
      · exact borrowed_waiting_step origin carriers receipt state waiting
    have remaining := ih (fun receipt member => preserved receipt (by simp [member]))
    simp only [List.forIn_cons, bind, first, remaining]

theorem actual_mixed_cancel_borrowed_retained (layout : LayoutEnv) (origin : OriginId)
    (receipts : List BorrowedWaitingExitReservation) (tokens : List Nat)
    (state : ExecutionState) (carriers : List Carrier) (pending : List PendingCarrierFrame)
    (preserved : ∀ receipt ∈ receipts,
      .pendingNamed receipt.token ∈ carriers ∨
        state.construction.exitReservations[receipt.token]? = some (.waiting receipt.incoming))
    (distinct : tokens.Nodup)
    (tickets : ∀ token ∈ tokens, CancelableExitTicket state token (carriers.filterMap fun carrier =>
      match carrier with | Carrier.completed id => some id | _ => none))
    (frames : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking layout state carrier)
    (separate : ∀ token ∈ tokens, ∀ frame ∈ pending, .completion token ∉ frame.channels) :
    ∃ after, exitChannelCleanupBorrowed origin receipts tokens true carriers state = .ok () after ∧
      ∀ frame ∈ pending, CarriersLandingReady after frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking layout after carrier := by
  have reversed : ∀ receipt ∈ receipts.reverse,
      .pendingNamed receipt.token ∈ carriers ∨
        state.construction.exitReservations[receipt.token]? = some (.waiting receipt.incoming) := by simpa using preserved
  have borrowed := borrowed_retained_or_waiting_loop origin carriers receipts.reverse state reversed
  obtain ⟨after, owned, result⟩ := actual_mixed_cancel_pending layout origin tokens state carriers pending distinct tickets frames separate
  have cleanup : exitChannelCleanupBorrowed origin receipts tokens true carriers state =
      exitChannelCleanupBorrowed origin [] tokens true carriers state := by
    simp only [exitChannelCleanupBorrowed, ↓reduceIte, List.reverse_nil, List.forIn_nil, bind, pure] at owned ⊢
    rw [borrowed]
  exact ⟨after, cleanup.trans owned, result⟩

#print axioms borrowed_retained_step
#print axioms borrowed_retained_or_waiting_loop
#print axioms actual_mixed_cancel_borrowed_retained

end Goose.Proofs.ConstructionAcceptedExecution
