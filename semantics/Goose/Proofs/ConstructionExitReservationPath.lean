import Goose.Proofs.ExitExecutionOwnedReceiptSetup
import Goose.Proofs.ConstructionExitByteBacking
import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsCleanupAncestry

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem accepted_fresh_reservation_replacement_path (config : EvalConfig) (initialized : Nat)
    (before reserved : ConstructionState) (incoming token selected : Nat)
    (execution : ExecutionState) (environment : RuntimeActivation)
    (scope : Nat) (scopeInst : Goose.Core.ScopeInst)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (valid : ReservationLifecycleInvariant before)
    (reservedExit : reserveExitDestination incoming .newValue before = .ok (token, selected) reserved)
    (construction : execution.construction = reserved)
    (world : AcceptedWorld config initialized execution ambient types live regions pending)
    (count : Nat) (openBacking : OpenDestinationBacking config.layout execution selected (.varr (.int .u8)) count)
    (different : ∀ snapshot, reserved.exitReservations[token]? = some (.active .fresh incoming selected snapshot) →
      selected ≠ snapshot.capability.id) :
    let unwound := releaseScopeState environment scope scopeInst execution
    ∃ snapshot owner,
      token = before.exitReservations.size ∧
      unwound.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot) ∧
      unwound.construction.destinations[snapshot.capability.id]? = some owner ∧
      openBacking.destination.use = .replacement snapshot.capability.id ∧
      openBacking.destination.backing = owner.backing ∧
      OwnershipReplacementPath unwound.construction.destinations snapshot.capability.id selected ∧
      ((∃ n, owner.progress = .exiting n selected) ∨ owner.progress = .abandoned ∨ owner.progress = .cancelled) := by
  obtain ⟨sameToken, snapshot, tickets⟩ := reserveExitDestination_active_push incoming .newValue before reserved token selected valid reservedExit
  have ticket : execution.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot) := by
    rw [construction, tickets, sameToken]
    simp
  have other : selected ≠ snapshot.capability.id := different snapshot (by simpa only [construction] using ticket)
  have role := world.ownership.source.aliases token incoming selected selected snapshot openBacking.destination ticket
    (.refl selected) openBacking.present
  simp only [if_neg other] at role
  have active : ReplacementSupported execution.construction selected :=
    .active selected openBacking.destination openBacking.present (by simp only [openBacking.opened, activeProgress])
  obtain ⟨owner, found, backing, progress⟩ := world.ownership.source.structural.1.2.2.1
    selected snapshot.capability.id openBacking.destination openBacking.present role.1 active
  exact ⟨snapshot, owner, sameToken, ticket, found, role.1, backing,
    .step selected snapshot.capability.id snapshot.capability.id openBacking.destination openBacking.present role.1 (.refl _), progress⟩

#print axioms accepted_fresh_reservation_replacement_path

end Goose.Proofs.ConstructionAcceptedExecution
