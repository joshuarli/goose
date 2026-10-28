import Goose.Proofs.ConstructionExitByteChildInvariants
import Goose.Proofs.ConstructionExitActiveRestore
import Goose.Proofs.ConstructionAcceptedByteSource

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem reserved_byte_build_cancel_restores_candidates (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (receiverState before after : ExecutionState) (reserved cleaned : ConstructionState)
    (incoming selected token count writeCount : Nat) (bytes : List UInt8) (origin : OriginId)
    (receiver : OpenDestinationBacking config.layout receiverState incoming (.varr (.int .u8)) (count + 1))
    (receiverCurrent : destinationCurrent receiverState.construction incoming = .ok incoming)
    (initialLifecycle : ReservationLifecycleInvariant receiverState.construction)
    (initialUnique : ActiveChildUnique receiverState.construction) (initialBlocked : ActiveChildParentBlocked receiverState.construction)
    (reservation : reserveExitDestination incoming .newValue receiverState.construction = .ok (token, selected) reserved)
    (construction : before.construction = reserved) (valid : OwnershipSourceState before.construction)
    (ready : OpenDestinationBacking config.layout before selected (.varr (.int .u8)) writeCount)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction selected = .ok selected)
    (built : buildExpr (fuel + 1) config environment selected (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after)
    (tree : abandonTree selected after.construction = .ok () cleaned) :
    ∃ final, cancelExitReservation token [] after.construction = .ok () final ∧
      ActiveChildUnique final ∧ ActiveChildParentBlocked final := by
  have correct : receiver.destination.capability.id = incoming := initialLifecycle.1.2.1 incoming receiver.destination receiver.present
  have fresh := reserve_open_replacement_fresh receiverState.construction reserved incoming selected token count
    receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes receiverCurrent reservation
  have receiverInside := (Array.getElem?_eq_some_iff.mp receiver.present).1
  have different : selected ≠ receiver.destination.capability.id := by rw [correct, fresh]; exact Ne.symm (Nat.ne_of_lt receiverInside)
  have reservedUnique := reserve_open_preserves_unique_children receiverState.construction reserved incoming selected token count
    receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes receiverCurrent initialUnique reservation
  have reservedBlocked := reserve_open_preserves_blocked_children receiverState.construction reserved incoming selected token count
    receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes receiverCurrent initialLifecycle.1.2.2.2 initialBlocked reservation
  have builtCandidates := build_packed_bytes_child_invariants fuel config environment selected writeCount bytes origin before after
    valid ready packed request current (by simpa only [construction] using reservedUnique)
    (by simpa only [construction] using reservedBlocked) built
  have noChildren := reserved_byte_build_preserves_snapshot_no_children fuel config environment receiverState before after reserved
    incoming selected token count writeCount bytes origin receiver receiverCurrent initialLifecycle.1.2.2.2 initialBlocked reservation
    construction valid ready packed request current built
  have parent := (reserve_open_receiver_snapshot receiverState.construction reserved incoming selected token count
    receiver.destination receiver.present receiver.opened receiverCurrent reservation).1
  have ticket := (reserve_open_receiver_snapshot receiverState.construction reserved incoming selected token count
    receiver.destination receiver.present receiver.opened receiverCurrent reservation).2
  have tickets := buildExpr_bytes_tickets fuel config environment selected (.varr (.int .u8)) bytes origin
    before after ready.destination writeCount valid current ready.present ready.opened built
  have afterTicket : after.construction.exitReservations[token]? = some (.active .fresh incoming selected receiver.destination) := by
    simpa only [tickets, construction] using ticket
  have incomingDifferent : incoming ≠ selected := by rw [fresh]; exact Nat.ne_of_lt receiverInside
  have unchanged := build_packed_bytes_other_row fuel config environment selected writeCount incoming bytes origin
    before after valid ready packed request current incomingDifferent built
  have parentAfter : after.construction.destinations[receiver.destination.capability.id]? =
      some { receiver.destination with progress := .exiting (count + 1) selected } := by
    simpa only [correct, unchanged, construction] using parent
  obtain ⟨finishedRow, finishedFound, sameCapability, finishedPhase⟩ :=
    build_packed_bytes_capability fuel config environment selected writeCount bytes origin before after valid ready packed request current built
  have source := buildExpr_bytes_sourceState fuel config environment selected (.varr (.int .u8)) bytes origin before after
    ready.destination writeCount valid current ready.present ready.opened built
  have terminal := destinationSuccessorKeysInactive_built_terminal after.construction source.inactiveKeys selected finishedRow finishedFound
    (writeCount + bytes.length) finishedPhase
  have selectedInside := (Array.getElem?_eq_some_iff.mp finishedFound).1
  have resolved : destinationCurrent after.construction selected = .ok selected := by
    simp only [destinationCurrent_result, destinationCurrentSteps_succ, selectedInside, ↓reduceIte, terminal]
  have authority : FreshReservationSnapshotAuthority after.construction := source.structural.1.2.1.2.2.2.2.1
  apply cancel_active_unblocked_snapshot_preserves_candidates after.construction cleaned token incoming selected selected
    receiver.destination finishedRow { receiver.destination with progress := .exiting (count + 1) selected } (count + 1)
    afterTicket resolved finishedFound (by simp [activeRow, finishedPhase]) tree different parentAfter rfl
    ⟨count + 1, Or.inl receiver.opened⟩ source.structural.1.1 authority _ builtCandidates.1 builtCandidates.2
  simpa only [correct] using noChildren

#print axioms reserved_byte_build_cancel_restores_candidates

end Goose.Proofs.ConstructionAcceptedExecution
