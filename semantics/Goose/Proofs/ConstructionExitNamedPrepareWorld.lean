import Goose.Proofs.ConstructionExitNamedMarkContext

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem prepareNamedCarrierAt_built (origin : OriginId) (state : ExecutionState)
    (token incoming count : Nat) (snapshot row : PendingDestination) (storage : ReceivingStorage) (stored : StoredValue)
    (current : destinationCurrent state.construction incoming = .ok incoming)
    (ticket : state.construction.exitReservations[token]? = some (.active (.named .awaitingSource) incoming incoming snapshot))
    (present : state.construction.destinations[incoming]? = some row) (built : row.progress = .built count)
    (storageFound : state.construction.storage[row.storage]? = some storage)
    (alias : stored.destination = some incoming) (sameStorage : row.storage = stored.storage)
    (sameStart : row.capability.start = stored.start) (type : stored.ty.adaptsTo row.capability.logicalType = true)
    (sameCount : count = stored.count) (startBound : row.capability.start ≤ row.writeEnd) (endBound : row.writeEnd ≤ storage.bytes.size) :
    let next := { row with progress := .built count }
    let after := { state with construction := { state.construction with exitReservations := state.construction.exitReservations.set! token (.active (.named .ready) incoming incoming next) } }
    markNamedReservation token state.construction = .ok () after.construction ∧
    prepareNamedCarrierAt origin token incoming stored state = .ok (some (.pendingNamed token)) after := by
  let next := { row with progress := .built count }
  let after := { state with construction := { state.construction with exitReservations := state.construction.exitReservations.set! token (.active (.named .ready) incoming incoming next) } }
  have startCheck : (row.capability.start > row.writeEnd) = false := by simp [Nat.not_lt_of_ge startBound]
  have endCheck : (row.writeEnd > storage.bytes.size) = false := by simp [Nat.not_lt_of_ge endBound]
  have marked : markNamedReservation token state.construction = .ok () after.construction := by
    simp only [markNamedReservation, ConstructionM.get, ticket, bind, pure, lookupDestination_result, present, built,
      lookupStorage_result, storageFound, startCheck, endCheck, ConstructionM.set]
    rfl
  refine ⟨marked, ?_⟩
  simp only [prepareNamedCarrierAt, receivingDestination, liftConstruction, current, bind, pure, EvalM.get,
    ticket, alias, Bool.not_true, Bool.false_or, ↓reduceIte, getDestination, present,
    built, sameStorage, sameStart, type, sameCount, marked, bne_self_eq_false, Bool.false_eq_true]
  simp [after, next, sameCount]

theorem prepareNamedCarrierAt_built_world (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (initial state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (origin : OriginId) (receipt : BorrowedWaitingExitReservation) (count : Nat)
    (snapshot row : PendingDestination) (storage : ReceivingStorage) (stored : StoredValue)
    (oldWorld : AcceptedWorld config initialized initial ambient types live regions pending)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (captured : receipt ∈ borrowedExitChannelReceipts activation initial)
    (current : destinationCurrent state.construction receipt.incoming = .ok receipt.incoming)
    (ticket : state.construction.exitReservations[receipt.token]? = some (.active (.named .awaitingSource) receipt.incoming receipt.incoming snapshot))
    (present : state.construction.destinations[receipt.incoming]? = some row) (built : row.progress = .built count)
    (storageFound : state.construction.storage[row.storage]? = some storage)
    (alias : stored.destination = some receipt.incoming) (sameStorage : row.storage = stored.storage)
    (sameStart : row.capability.start = stored.start) (type : stored.ty.adaptsTo row.capability.logicalType = true)
    (sameCount : count = stored.count) (startBound : row.capability.start ≤ row.writeEnd) (endBound : row.writeEnd ≤ storage.bytes.size) :
    ∃ after, prepareNamedCarrierAt origin receipt.token receipt.incoming stored state = .ok (some (.pendingNamed receipt.token)) after ∧
      AcceptedWorld config initialized after ambient types live regions pending := by
  let next := { row with progress := .built count }
  let after := { state with construction := { state.construction with exitReservations := state.construction.exitReservations.set! receipt.token (.active (.named .ready) receipt.incoming receipt.incoming next) } }
  have result := prepareNamedCarrierAt_built origin state receipt.token receipt.incoming count snapshot row storage stored current ticket present built
    storageFound alias sameStorage sameStart type sameCount startBound endBound
  refine ⟨after, result.2, ?_⟩
  exact mark_named_accepted_world config initialized activation initial state after.construction receipt.token receipt.incoming receipt.incoming snapshot
    ambient types live regions pending oldWorld world receipt captured rfl ticket result.1

#print axioms prepareNamedCarrierAt_built_world
#print axioms prepareNamedCarrierAt_built

end Goose.Proofs.ConstructionAcceptedExecution
