import Goose.Proofs.ExitExecutionUnwind
import Goose.Proofs.ConstructionExecutionOwnershipReservations
import Goose.Proofs.ConstructionExitByteReplacement
import Goose.Proofs.ConstructionExitByteReservation

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionRepresentation

theorem withExitChannels_single_completed_cleanup (source target : RuntimeActivation)
    (operand : Expr) (origin : Goose.Core.OriginId) (action : List Channel → EvalM (List Carrier))
    (initial prepared built : ExecutionState) (selected token incoming : Nat) (snapshot : PendingDestination)
    (setup : exitChannels source target [operand] origin initial = .ok [.construct selected] prepared)
    (tokens : exitChannelReservationTokens initial.construction.exitReservations.size prepared = [token])
    (evaluated : action [.construct selected] prepared = .ok [.completed selected] built)
    (ticket : built.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot)) :
    withExitChannels source target [operand] origin action initial = .ok [.completed selected]
      { built with construction := { built.construction with
        exitReservations := built.construction.exitReservations.set! token .released } } := by
  have released := releaseExitReservation_active built.construction token .fresh incoming selected snapshot ticket
  simp only [withExitChannels_decomposition, setup, evaluated, tokens, materializeOwnedCarriers, List.mapM_cons, List.mapM_nil, bind, pure,
    finishBorrowedExitChannels, exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.forIn_cons, List.forIn_nil,
    liftConstruction, released]

theorem returnFrom_single_completed_cleanup (fuel : Nat) (config : EvalConfig)
    (source target : RuntimeActivation) (targetId : Nat) (operand : Expr) (origin : Goose.Core.OriginId)
    (initial prepared built : ExecutionState) (selected token incoming : Nat) (snapshot : PendingDestination)
    (selection : targetActivation config targetId initial = .ok target initial)
    (setup : exitChannels source target [operand] origin initial = .ok [.construct selected] prepared)
    (tokens : exitChannelReservationTokens initial.construction.exitReservations.size prepared = [token])
    (evaluated : evalOperands fuel config source [.construct selected] [operand] prepared = .ok [.completed selected] built)
    (ticket : built.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot)) :
    let cleaned := { built with construction := { built.construction with
      exitReservations := built.construction.exitReservations.set! token .released } }
    execStmt (fuel + 1) config source (.returnFrom targetId [operand] origin) initial =
      .escape ⟨target.act, .nonlocal targetId⟩ [.completed selected] cleaned ∧
    cleaned.construction.destinations = built.construction.destinations ∧
    cleaned.construction.storage = built.construction.storage ∧
    cleaned.objects = built.objects := by
  have completion := withExitChannels_single_completed_cleanup source target operand origin
    (fun channels => evalOperands fuel config source channels [operand]) initial prepared built selected token incoming snapshot
    setup tokens evaluated ticket
  simp only [execStmt, bind, selection, completion, Goose.Construct.escaped, and_self]

theorem accepted_byte_replacement_operands (fuel : Nat) (config : EvalConfig)
    (initialized : Nat) (source : RuntimeActivation) (bytes : List UInt8)
    (origin : Goose.Core.OriginId) (id parent count : Nat) (before after : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (replacement : ready.destination.use = .replacement parent) (fits : count + bytes.length < 2 ^ 32)
    (current : destinationCurrent before.construction id = .ok id)
    (built : buildExpr (fuel + 1) config source id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    evalOperands (fuel + 3) config source [.construct id] [.bytes (.varr (.int .u8)) bytes origin] before =
      .ok [.completed id] after := by
  have produced := (accepted_byte_replacement_produce_unwind fuel config initialized source bytes origin id parent count
    before after ambient types live regions pending world ready packed request replacement fits current built 0 0).1
  simp only [evalOperands, produced, bind, singleCarrier, pure]

theorem accepted_returnFrom_byte_replacement_cleanup (fuel : Nat) (config : EvalConfig)
    (initialized : Nat) (source target : RuntimeActivation) (targetId : Nat) (bytes : List UInt8)
    (origin : Goose.Core.OriginId) (id parent token incoming count : Nat) (snapshot : PendingDestination)
    (initial prepared after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (selection : targetActivation config targetId initial = .ok target initial)
    (setup : exitChannels source target [.bytes (.varr (.int .u8)) bytes origin] origin initial = .ok [.construct id] prepared)
    (tokens : exitChannelReservationTokens initial.construction.exitReservations.size prepared = [token])
    (ticket : prepared.construction.exitReservations[token]? = some (.active .fresh incoming id snapshot))
    (world : AcceptedWorld config initialized prepared ambient types live regions pending)
    (ready : OpenDestinationBacking config.layout prepared id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (replacement : ready.destination.use = .replacement parent) (fits : count + bytes.length < 2 ^ 32)
    (current : destinationCurrent prepared.construction id = .ok id)
    (built : buildExpr (fuel + 1) config source id (.bytes (.varr (.int .u8)) bytes origin) prepared = .ok () after) :
    let cleaned := { after with construction := { after.construction with
      exitReservations := after.construction.exitReservations.set! token .released } }
    execStmt (fuel + 4) config source (.returnFrom targetId [.bytes (.varr (.int .u8)) bytes origin] origin) initial =
      .escape ⟨target.act, .nonlocal targetId⟩ [.completed id] cleaned ∧
    cleaned.construction.destinations = after.construction.destinations ∧
    cleaned.construction.storage = after.construction.storage ∧ cleaned.objects = after.objects := by
  have evaluated := accepted_byte_replacement_operands fuel config initialized source bytes origin id parent count
    prepared after ambient types live regions pending world ready packed request replacement fits current built
  have tickets := buildExpr_bytes_tickets fuel config source id (.varr (.int .u8)) bytes origin prepared after
    ready.destination count world.ownership.source current ready.present ready.opened built
  have builtTicket : after.construction.exitReservations[token]? = some (.active .fresh incoming id snapshot) := by
    simpa only [tickets] using ticket
  exact returnFrom_single_completed_cleanup (fuel + 3) config source target targetId
    (.bytes (.varr (.int .u8)) bytes origin) origin initial prepared after id token incoming snapshot
    selection setup tokens evaluated builtTicket

#print axioms accepted_returnFrom_byte_replacement_cleanup
#print axioms accepted_byte_replacement_operands
#print axioms returnFrom_single_completed_cleanup
#print axioms withExitChannels_single_completed_cleanup

end Goose.Proofs.ExitExecution
