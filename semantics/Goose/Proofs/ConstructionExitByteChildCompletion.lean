import Goose.Proofs.ConstructionExitByteChildReady
import Goose.Proofs.ConstructionExitByteLand

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem reserved_byte_child_completion_landing (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (reservationBefore reserved : ConstructionState) (incoming selected token count writeCount : Nat)
    (receiverState : ExecutionState) (receiverConstruction : receiverState.construction = reservationBefore)
    (receiver : OpenDestinationBacking config.layout receiverState incoming (.varr (.int .u8)) (count + 1))
    (parentId parentCount : Nat) (parent : PendingDestination)
    (parentFound : reservationBefore.destinations[parentId]? = some parent)
    (parentPhase : parent.progress = .suspended parentCount incoming) (receiverUse : receiver.destination.use = .child parentId)
    (ordered : DestinationOwnersOrdered reservationBefore)
    (receiverCurrent : destinationCurrent reservationBefore incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue reservationBefore = .ok (token, selected) reserved)
    (environment : RuntimeActivation) (before after : ExecutionState) (construction : before.construction = reserved)
    (ambient : OwnershipAmbient) (channels : List Channel) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before (.exitChannels [token] channels [.completed selected] :: ambient) types live regions pending)
    (completion completionIncoming : Nat) (completionRole : ExitReservationRole) (completionSnapshot : PendingDestination)
    (differentTokens : token ≠ completion)
    (completionTicket : before.construction.exitReservations[completion]? =
      some (.active completionRole completionIncoming incoming completionSnapshot))
    (ready : OpenDestinationBacking config.layout before selected (.varr (.int .u8)) writeCount)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (bytes : List UInt8) (fits : writeCount + bytes.length < 2 ^ 32)
    (selectedCurrent : destinationCurrent before.construction selected = .ok selected) (origin : OriginId)
    (built : buildExpr (fuel + 1) config environment selected (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after)
    (scope scopeInst : Nat) :
    incoming ≠ selected ∧ ∃ cleaned landed,
      exitChannelCleanupBorrowed origin [] [token] false [.completed selected] after = .ok () cleaned ∧
      landCarriersInto origin [.completion completion] [.completed selected] (releaseScopeState environment scope scopeInst cleaned) = .ok () landed ∧
      CarrierResultBacking config.layout landed (.completed selected) ∧
      CarrierLandingReady landed (.completion completion) (.completed selected) := by
  have receiverPresent : reservationBefore.destinations[incoming]? = some receiver.destination := by
    simpa only [receiverConstruction] using receiver.present
  have receiverStored : reservationBefore.storage[receiver.destination.storage]? = some receiver.storage := by
    simpa only [receiverConstruction] using receiver.bytes
  have fresh := reserve_open_replacement_fresh reservationBefore reserved incoming selected token count receiver.destination receiver.storage
    receiverPresent receiver.opened receiverStored receiverCurrent reservation
  have distinct : incoming ≠ selected := by rw [fresh]; exact Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp receiverPresent).1
  have ticket : before.construction.exitReservations[token]? = some (.active .fresh incoming selected receiver.destination) := by
    simpa only [construction] using (reserve_open_receiver_snapshot reservationBefore reserved incoming selected token count receiver.destination
      receiverPresent receiver.opened receiverCurrent reservation).2
  obtain ⟨cleaned, cleanup, context⟩ := build_packed_bytes_cleanup_context fuel config environment selected writeCount token incoming
    receiver.destination bytes origin before after channels [.completed selected] ambient world.ownership ticket ready packed request selectedCurrent built scope scopeInst
  have tickets := buildExpr_bytes_tickets fuel config environment selected (.varr (.int .u8)) bytes origin before after
    ready.destination writeCount world.ownership.source selectedCurrent ready.present ready.opened built
  have afterTicket : after.construction.exitReservations[token]? = some (.active .fresh incoming selected receiver.destination) := by
    simpa only [tickets] using ticket
  have released := releaseExitReservation_active after.construction token .fresh incoming selected receiver.destination afterTicket
  have exactCleanup : exitChannelCleanupBorrowed origin [] [token] false [.completed selected] after =
      .ok () { after with construction := { after.construction with
        exitReservations := after.construction.exitReservations.set! token .released } } := by
    simp only [exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.forIn_cons, List.forIn_nil, liftConstruction, released, bind, pure]
  have equal := cleanup.symm.trans exactCleanup
  cases equal
  have completionAfter : (releaseScopeState environment scope scopeInst { after with construction := { after.construction with
      exitReservations := after.construction.exitReservations.set! token .released } }).construction.exitReservations[completion]? =
      some (.active completionRole completionIncoming incoming completionSnapshot) := by
    simp only [releaseScopeState, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne differentTokens, tickets, completionTicket]
  obtain ⟨⟨landingReady⟩, backed⟩ := reserved_byte_child_landing_ready fuel config initialized reservationBefore reserved incoming selected token count writeCount
    receiverState receiverConstruction receiver parentId parentCount parent parentFound parentPhase receiverUse ordered receiverCurrent reservation
    environment before after construction (.exitChannels [token] channels [.completed selected] :: ambient) types live regions pending
    world ready packed request bytes fits selectedCurrent origin built scope scopeInst
  obtain ⟨landed, success, landedBacking, postReady, _⟩ := landCarriersInto_completion_completed config.layout origin
    (releaseScopeState environment scope scopeInst { after with construction := { after.construction with
      exitReservations := after.construction.exitReservations.set! token .released } })
    (.returned [.completed selected] :: ambient) completion completionIncoming incoming selected completionRole completionSnapshot
    context completionAfter backed landingReady
  exact ⟨distinct, _, landed, cleanup, success, landedBacking, postReady⟩

#print axioms reserved_byte_child_completion_landing

end Goose.Proofs.ConstructionAcceptedExecution
