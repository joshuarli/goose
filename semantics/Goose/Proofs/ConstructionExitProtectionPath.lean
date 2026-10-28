import Goose.Proofs.ConstructionExitProtectionCleanup
import Goose.Proofs.ConstructionExitByteReservation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem reserved_byte_unwind_protection (fuel : Nat) (config : EvalConfig)
    (environment inner outer : RuntimeActivation) (before after : ExecutionState) (reserved : ConstructionState)
    (incoming selected token count writeCount : Nat) (bytes : List UInt8) (origin : OriginId)
    (innerScope outerScope : Nat) (innerInst outerInst : ScopeInst)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (receiverCurrent : destinationCurrent before.construction incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (valid : OwnershipSourceState reserved)
    (ready : OpenDestinationBacking config.layout { before with construction := reserved } selected (.varr (.int .u8)) writeCount)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent reserved selected = .ok selected)
    (live : RootInst → Prop) (region : ReceivingRegion)
    (destination : region.destination = incoming) (protection : ReceivingProtection config.layout before live region)
    (built : buildExpr (fuel + 1) config environment selected (.bytes (.varr (.int .u8)) bytes origin)
      { before with construction := reserved } = .ok () after)
    (innerOutside : ∀ root, live root → ¬ region.mutableRoots root →
      (Goose.Proofs.Exit.runtimeScopeRoots inner innerScope innerInst).contains root = false)
    (outerOutside : ∀ root, live root → ¬ region.mutableRoots root →
      (Goose.Proofs.Exit.runtimeScopeRoots outer outerScope outerInst).contains root = false) :
    ∃ cleaned, exitChannelCleanupBorrowed origin [] [token] false [.completed selected] after = .ok () cleaned ∧
      let first := releaseScopeState inner innerScope innerInst cleaned
      let crossed := { first with activations := first.activations.filter (fun current => current.act != inner.act) }
      let second := releaseScopeState outer outerScope outerInst crossed
      let final := { second with activations := second.activations.filter (fun current => current.act != outer.act) }
      ReceivingProtection config.layout final live { region with mutableDestinations := selected :: region.mutableDestinations } := by
  have builtProtection := reserved_packed_byte_build_protection fuel config environment before reserved after incoming selected token
    count writeCount bytes origin receiver receiverCurrent reservation valid ready packed request current live region destination protection built
  have ticket := (reserve_open_receiver_snapshot before.construction reserved incoming selected token count receiver.destination
    receiver.present receiver.opened receiverCurrent reservation).2
  have tickets := buildExpr_bytes_tickets fuel config environment selected (.varr (.int .u8)) bytes origin
    { before with construction := reserved } after ready.destination writeCount valid current ready.present ready.opened built
  have afterTicket : after.construction.exitReservations[token]? = some (.active .fresh incoming selected receiver.destination) := by
    simpa only [tickets] using ticket
  exact receivingProtection_cleanup_two_scopes config.layout after live
    { region with mutableDestinations := selected :: region.mutableDestinations } token incoming selected receiver.destination origin
    [.completed selected] inner outer innerScope outerScope innerInst outerInst afterTicket innerOutside outerOutside builtProtection

#print axioms reserved_byte_unwind_protection

end Goose.Proofs.ConstructionAcceptedExecution
