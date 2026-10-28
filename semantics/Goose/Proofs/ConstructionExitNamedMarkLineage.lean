import Goose.Proofs.ConstructionExitNamedActivationContext

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem mark_named_preserves_selected (state after : ConstructionState) (token incoming : Nat) (snapshot : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active (.named .awaitingSource) incoming incoming snapshot))
    (marked : markNamedReservation token state = .ok () after) :
    ∃ next, after.exitReservations[token]? = some (.active (.named .ready) incoming incoming next) := by
  simp only [markNamedReservation, ConstructionM.get, ticket, bind, pure, lookupDestination_result] at marked
  cases present : state.destinations[incoming]? with
  | none => simp [present, ConstructionM.fail] at marked
  | some row =>
    simp only [present] at marked
    cases progress : row.progress <;> simp only [progress] at marked <;> try (simp [ConstructionM.fail] at marked)
    all_goals
      simp only [pure, lookupStorage_result, bind] at marked
      cases stored : state.storage[row.storage]? with
      | none => simp [stored, ConstructionM.fail] at marked
      | some storage =>
        simp only [stored] at marked
        split at marked
        · simp [ConstructionM.fail] at marked
        · simp only [ConstructionM.get, ConstructionM.set, bind, pure, ConstructionResult.ok.injEq, true_and] at marked
          subst after
          have inside := (Array.getElem?_eq_some_iff.mp ticket).1
          simp [Array.set!_eq_setIfInBounds, inside]

theorem marked_borrowed_rearm_world (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (initial before after : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (origin : Goose.Core.OriginId) (carriers : List Carrier) (receipt : BorrowedWaitingExitReservation)
    (snapshot row : PendingDestination) (current : Nat)
    (oldWorld : AcceptedWorld config initialized initial ambient types live regions pending)
    (world : AcceptedWorld config initialized after ambient types live regions pending)
    (captured : receipt ∈ borrowedExitChannelReceipts activation initial)
    (ticket : before.construction.exitReservations[receipt.token]? = some (.active (.named .awaitingSource) receipt.incoming receipt.incoming snapshot))
    (marked : markNamedReservation receipt.token before.construction = .ok () after.construction)
    (resolved : destinationCurrent after.construction receipt.incoming = .ok current)
    (present : after.construction.destinations[current]? = some row)
    (unretained : (carriers.any fun carrier => match carrier with
      | .pendingNamed actual => actual == receipt.token | _ => false) = false) :
    ∃ final, borrowedExitChannelStep origin carriers receipt after = .ok (ForInStep.yield PUnit.unit) final ∧
      AcceptedWorld config initialized final ambient types live regions pending := by
  obtain ⟨next, active⟩ := mark_named_preserves_selected before.construction after.construction receipt.token receipt.incoming snapshot ticket marked
  exact borrowed_named_step_accepted_world config initialized activation initial after ambient types live regions pending
    origin carriers receipt .ready receipt.incoming receipt.incoming current next row oldWorld world captured active resolved resolved present unretained

#print axioms marked_borrowed_rearm_world
#print axioms mark_named_preserves_selected

end Goose.Proofs.ConstructionAcceptedExecution
