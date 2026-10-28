import Goose.Proofs.ConstructionExitReceiverCurrent

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem reserved_byte_receiver_parent (fuel : Nat) (config : EvalConfig)
    (reservationBefore reserved : ConstructionState) (incoming selected token count writeCount : Nat)
    (original : PendingDestination) (present : reservationBefore.destinations[incoming]? = some original)
    (opened : original.progress = .open (count + 1)) (receiver : original.use = .receiver)
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
    let unwound := releaseScopeState environment scope scopeInst cleaned
    let parent := { original with progress := .exiting (count + 1) selected }
    destinationCurrent unwound.construction incoming = .ok incoming ∧
    unwound.construction.destinations[incoming]? = some parent ∧
    LandingParentReady unwound.construction incoming parent := by
  have current := reserved_byte_receiver_current fuel config reservationBefore reserved incoming selected token count writeCount
    original present opened receiverCurrent reservation environment before after construction valid ready packed request
    selectedCurrent bytes origin built scope scopeInst
  have parent := reserved_parent_survives_byte_build fuel config reservationBefore reserved incoming selected token count writeCount
    original present opened receiverCurrent reservation environment before after construction valid ready packed request
    selectedCurrent bytes origin built scope scopeInst
  exact ⟨current, parent, .receiver receiver⟩

theorem completed_carrier_after_ticket_release (layout : LayoutEnv) (state : ExecutionState)
    (token id : Nat) (backed : CarrierResultBacking layout state (.completed id)) :
    CarrierResultBacking layout { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token .released } } (.completed id) := by
  cases backed with
  | completed id count destination stored present built sampled backing =>
    refine .completed id count destination stored present built ?_ ?_
    · simp only [storedDestination, getDestination, EvalM.get, bind, pure] at sampled ⊢
      cases found : state.construction.destinations[id]? with
      | none => simp [found, fault, EvalM.stop] at sampled
      | some row =>
        simp only [found] at sampled ⊢
        cases progress : progressCount row.progress with
        | none => simp [progress, fault, EvalM.stop] at sampled
        | some n => simp only [progress, ExecutionStep.ok.injEq] at sampled ⊢; exact sampled
    · cases backing with
      | detached receiving element present detached ty interval =>
        exact .detached receiving element present detached ty interval
      | named id receiving destination count present named binding backing ty start progress element elementType interval =>
        exact .named id receiving destination count present named binding backing ty start progress element elementType interval

theorem completed_carrier_after_cleanup_unwind (layout : LayoutEnv) (state : ExecutionState)
    (token id : Nat) (environment : RuntimeActivation) (scope : Nat) (scopeInst : Goose.Core.ScopeInst)
    (backed : CarrierResultBacking layout state (.completed id)) :
    let cleaned := { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token .released } }
    CarrierResultBacking layout (releaseScopeState environment scope scopeInst cleaned) (.completed id) := by
  let cleaned := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! token .released } }
  exact carrierBacking_construction_frame layout cleaned (releaseScopeState environment scope scopeInst cleaned)
    rfl _ (completed_carrier_after_ticket_release layout state token id backed)

#print axioms completed_carrier_after_cleanup_unwind
#print axioms completed_carrier_after_ticket_release
#print axioms reserved_byte_receiver_parent

end Goose.Proofs.ConstructionAcceptedExecution
