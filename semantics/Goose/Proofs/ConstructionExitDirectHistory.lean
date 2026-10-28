import Goose.Proofs.ConstructionExitDirectSourceRoles
import Goose.Proofs.ConstructionExitReservationHistoryFrames
import Goose.Proofs.ConstructionExitSingleCleanup

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem direct_byte_reservation_history (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (bytes : List UInt8) (origin : OriginId) (before : ExecutionState) (id : Nat)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (source : OwnershipSourceState before.construction) (ambient : OwnershipAmbient)
    (history : ReservationReferencesBounded before.construction ambient)
    (receiver : ready.destination.use = .receiver) (packed : ready.destination.layout = .packed)
    (adaptation : ready.destination.adaptation = none) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32) :
    let token := before.construction.exitReservations.size
    let reserved := { before.construction with exitReservations := before.construction.exitReservations.push (.active .fresh id id ready.destination) }
    let prepared := { before with construction := reserved }
    ∃ after cleaned : ExecutionState,
      reserveExitDestination id .newValue before.construction = .ok (token, id) reserved ∧
      buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) prepared = .ok () after ∧
      ReservationReferencesBounded after.construction (.exitChannels [token] [.construct id] [.completed id] :: ambient) ∧
      exitChannelCleanupBorrowed origin [] [token] false [.completed id] after = .ok () cleaned ∧
      ReservationReferencesBounded cleaned.construction ambient := by
  let token := before.construction.exitReservations.size
  let reserved := { before.construction with exitReservations := before.construction.exitReservations.push (.active .fresh id id ready.destination) }
  let prepared := { before with construction := reserved }
  have reservation := reserve_open_zero_direct before.construction id ready.destination ready.present ready.opened current
  have reservedSource := direct_fresh_source_state before.construction id ready.destination source ready.present ready.opened current
  have reservedCurrent : destinationCurrent reserved id = .ok id := by
    rw [destinationCurrent_congr_tables before.construction reserved rfl rfl id]
    exact current
  obtain ⟨after, built⟩ := packed_receiver_byte_build fuel config environment bytes origin prepared id 0
    ready.destination ready.storage ready.present ready.bytes ready.opened packed adaptation receiver request reservedCurrent (by simpa using fits)
  have tickets := buildExpr_bytes_tickets fuel config environment id (.varr (.int .u8)) bytes origin prepared after
    ready.destination 0 reservedSource reservedCurrent ready.present ready.opened built
  have bounded := fresh_reservation_references_bounded before.construction reserved ambient id id token
    [.construct id] [.completed id] source.structural.1.1 history reservation
  have afterBounded : ReservationReferencesBounded after.construction (.exitChannels [token] [.construct id] [.completed id] :: ambient) := by
    apply reservationReferencesBounded_mono reserved after.construction _ _ bounded
    simp only [tickets]
    exact Nat.le_refl _
  have ticket : after.construction.exitReservations[token]? = some (.active .fresh id id ready.destination) := by
    rw [tickets]
    simp [prepared, reserved, token]
  let cleaned := { after with construction := { after.construction with
    exitReservations := after.construction.exitReservations.set! token .released } }
  have released := releaseExitReservation_active after.construction token .fresh id id ready.destination ticket
  have cleanup : exitChannelCleanupBorrowed origin [] [token] false [.completed id] after = .ok () cleaned := by
    simp only [exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.forIn_cons, List.forIn_nil, liftConstruction, released, bind, pure]
    rfl
  have afterRelease := reservationReferencesBounded_release after.construction cleaned.construction
    (.exitChannels [token] [.construct id] [.completed id] :: ambient) token afterBounded released
  exact ⟨after, cleaned, reservation, built, afterBounded, cleanup,
    reservationReferencesBounded_pop cleaned.construction _ ambient afterRelease⟩

#print axioms direct_byte_reservation_history

end Goose.Proofs.ConstructionAcceptedExecution
