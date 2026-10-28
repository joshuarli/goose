import Goose.Proofs.ConstructionExitByteFinishParent
import Goose.Proofs.ConstructionExitByteSetup

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem exiting_receiver_current_after_cleanup (state : ExecutionState) (id count selected token : Nat)
    (row : PendingDestination) (valid : OwnershipSourceState state.construction)
    (present : state.construction.destinations[id]? = some row)
    (exiting : row.progress = .exiting count selected)
    (environment : RuntimeActivation) (scope : Nat) (scopeInst : Goose.Core.ScopeInst) :
    let cleaned := { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token .released } }
    destinationCurrent (releaseScopeState environment scope scopeInst cleaned).construction id = .ok id := by
  have terminal := destinationSuccessorKeysInactive_live_terminal state.construction valid.inactiveKeys id row present
    (by simp only [exiting, activeProgress])
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  simp only [releaseScopeState, destinationCurrent_result, destinationCurrentSteps_succ, inside, ↓reduceIte, terminal]

theorem reserved_byte_receiver_current (fuel : Nat) (config : EvalConfig)
    (reservationBefore reserved : ConstructionState) (incoming selected token count writeCount : Nat)
    (original : PendingDestination) (present : reservationBefore.destinations[incoming]? = some original)
    (opened : original.progress = .open (count + 1))
    (receiverCurrent : destinationCurrent reservationBefore incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue reservationBefore = .ok (token, selected) reserved)
    (environment : RuntimeActivation) (before after : ExecutionState) (construction : before.construction = reserved)
    (valid : OwnershipSourceState before.construction)
    (ready : OpenDestinationBacking config.layout before selected (.varr (.int .u8)) writeCount)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (selectedCurrent : destinationCurrent before.construction selected = .ok selected)
    (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (built : buildExpr (fuel + 1) config environment selected (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after)
    (scope : Nat) (scopeInst : Goose.Core.ScopeInst) :
    let cleaned := { after with construction := { after.construction with
      exitReservations := after.construction.exitReservations.set! token .released } }
    destinationCurrent (releaseScopeState environment scope scopeInst cleaned).construction incoming = .ok incoming := by
  have parent := reserved_parent_survives_byte_build fuel config reservationBefore reserved incoming selected token count writeCount
    original present opened receiverCurrent reservation environment before after construction valid ready packed request
    selectedCurrent bytes origin built scope scopeInst
  have source := buildExpr_bytes_sourceState fuel config environment selected (.varr (.int .u8)) bytes origin
    before after ready.destination writeCount valid selectedCurrent ready.present ready.opened built
  exact exiting_receiver_current_after_cleanup after incoming (count + 1) selected token _ source parent rfl environment scope scopeInst

#print axioms exiting_receiver_current_after_cleanup
#print axioms reserved_byte_receiver_current

end Goose.Proofs.ConstructionAcceptedExecution
