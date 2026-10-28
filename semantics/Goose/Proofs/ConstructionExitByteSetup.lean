import Goose.Proofs.ConstructionExitSingleCleanup
import Goose.Proofs.ConstructionExitOpenReservation
import Goose.Proofs.ExitExecutionOwnedReceiptSetup
import Goose.Proofs.ConstructionExitByteFinishParent

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionRepresentation

theorem byte_exitChannels_fresh_setup (source target : RuntimeActivation) (bytes : List UInt8)
    (origin : Goose.Core.OriginId) (initial : ExecutionState) (incoming selected token count : Nat)
    (row : PendingDestination) (reserved : ConstructionState)
    (channels : target.channels = [.construct incoming])
    (present : initial.construction.destinations[incoming]? = some row)
    (opened : row.progress = .open (count + 1))
    (current : destinationCurrent initial.construction incoming = .ok incoming)
    (valid : ReservationLifecycleInvariant initial.construction)
    (reservation : reserveExitDestination incoming .newValue initial.construction = .ok (token, selected) reserved) :
    let prepared := { initial with construction := reserved }
    exitChannels source target [.bytes (.varr (.int .u8)) bytes origin] origin initial =
      .ok [.construct selected] prepared ∧
    exitChannelReservationTokens initial.construction.exitReservations.size prepared = [token] ∧
    prepared.construction.exitReservations[token]? = some (.active .fresh incoming selected row) ∧
    prepared.construction.destinations[incoming]? = some { row with progress := .exiting (count + 1) selected } := by
  have ⟨parent, ticket⟩ := Goose.Proofs.ConstructionAcceptedExecution.reserve_open_receiver_snapshot
    initial.construction reserved incoming selected token count row present opened current reservation
  obtain ⟨tokenEq, snapshot, tickets⟩ := reserveExitDestination_active_push incoming .newValue
    initial.construction reserved token selected valid reservation
  refine ⟨?_, ?_, ticket, parent⟩
  · simp only [exitChannels, channels, List.length_cons, List.length_nil, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.mapM_cons,
      List.mapM_nil, exitSource, receivingDestination, liftConstruction, current, bind, pure, reservation]
  · simp only [exitChannelReservationTokens, tickets, Array.size_push, Nat.add_sub_cancel_left,
      List.range_one, List.map_cons, List.map_nil, Nat.add_zero, tokenEq]

theorem accepted_open_byte_return (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (source target : RuntimeActivation) (targetId incoming selected token count writeCount : Nat)
    (bytes : List UInt8) (origin : Goose.Core.OriginId) (initial after : ExecutionState)
    (row : PendingDestination) (reserved : ConstructionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame)
    (selection : targetActivation config targetId initial = .ok target initial)
    (channels : target.channels = [.construct incoming])
    (present : initial.construction.destinations[incoming]? = some row)
    (opened : row.progress = .open (count + 1))
    (receiverCurrent : destinationCurrent initial.construction incoming = .ok incoming)
    (valid : ReservationLifecycleInvariant initial.construction)
    (reservation : reserveExitDestination incoming .newValue initial.construction = .ok (token, selected) reserved)
    (world : AcceptedWorld config initialized { initial with construction := reserved } ambient types live regions pending)
    (ready : OpenDestinationBacking config.layout { initial with construction := reserved } selected (.varr (.int .u8)) writeCount)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (fits : writeCount + bytes.length < 2 ^ 32)
    (current : destinationCurrent reserved selected = .ok selected)
    (built : buildExpr (fuel + 1) config source selected (.bytes (.varr (.int .u8)) bytes origin)
      { initial with construction := reserved } = .ok () after) :
    let cleaned := { after with construction := { after.construction with
      exitReservations := after.construction.exitReservations.set! token .released } }
    execStmt (fuel + 4) config source (.returnFrom targetId [.bytes (.varr (.int .u8)) bytes origin] origin) initial =
      .escape ⟨target.act, .nonlocal targetId⟩ [.completed selected] cleaned ∧
    cleaned.construction.destinations[incoming]? = some { row with progress := .exiting (count + 1) selected } ∧
    cleaned.construction.storage = after.construction.storage := by
  obtain ⟨setup, tokens, ticket, initialParent⟩ := byte_exitChannels_fresh_setup source target bytes origin initial
    incoming selected token count row reserved channels present opened receiverCurrent valid reservation
  have distinct : selected ≠ incoming := by
    intro equal
    have same : { row with progress := .exiting (count + 1) selected } = ready.destination := by
      apply Option.some.inj
      rw [← equal] at initialParent
      exact initialParent.symm.trans ready.present
    have impossible := congrArg PendingDestination.progress same
    simp only [ready.opened] at impossible
    cases impossible
  have rowId : row.capability.id = incoming := valid.1.2.1 incoming row present
  have roles := world.ownership.source.aliases token incoming selected selected row ready.destination ticket
    (.refl selected) ready.present
  simp only [rowId, if_neg distinct] at roles
  have replacement : ready.destination.use = .replacement incoming := roles.1
  have result := accepted_returnFrom_byte_replacement_cleanup fuel config initialized source target targetId bytes origin
    selected incoming token incoming writeCount row initial { initial with construction := reserved } after ambient types live regions pending
    selection setup tokens ticket world ready packed request replacement fits current built
  have parent := reserved_parent_survives_byte_build fuel config initial.construction reserved incoming selected token count writeCount
    row present opened receiverCurrent reservation source { initial with construction := reserved } after rfl world.ownership.source
    ready packed request current bytes origin built 0 0
  exact ⟨result.1, parent, rfl⟩

#print axioms accepted_open_byte_return
#print axioms byte_exitChannels_fresh_setup

end Goose.Proofs.ExitExecution
