import Goose.Proofs.ConstructionExitWaitingSource
import Goose.Proofs.ConstructionExitWaitingCarrier
import Goose.Proofs.ConstructionExitEvaluationHistoryNumericOperands

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

theorem appended_ticket_value_backing (layout : LayoutEnv) (before : ExecutionState) (reservation : ExitReservation)
    (value : Value) (backed : ValueStorageBacked layout before value) :
    ValueStorageBacked layout { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push reservation } } value := by
  have storedBacking (stored : StoredValue) (backed : StoredValueBacking layout before stored) :
      StoredValueBacking layout { before with construction := { before.construction with
        exitReservations := before.construction.exitReservations.push reservation } } stored := by
    cases backed with
    | detached storage element present detached type interval => exact .detached storage element present detached type interval
    | named id storage destination count present named binding backing type start progress element elementType interval =>
      exact .named id storage destination count present named binding backing type start progress element elementType interval
  induction backed with
  | integer ty value => exact .integer ty value
  | boolean value => exact .boolean value
  | unit => exact .unit
  | reference location => exact .reference location
  | slice location start count => exact .slice location start count
  | stored value backed => exact .stored value (storedBacking value backed)
  | array values children ih => exact .array values ih
  | record id values children ih => exact .record id values ih

theorem appended_ticket_stored_observation (layout : LayoutEnv) (before : ExecutionState) (reservation : ExitReservation)
    (limit : Nat → Nat) (stored : StoredValue) (observed : StoredBackingObservation layout before limit stored) :
    StoredBackingObservation layout { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push reservation } } limit stored := by
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push reservation } }
  obtain ⟨storage, run, fuel, finish, found, sampled, measured, lower, upper⟩ := observed.observed
  change StoredBackingObservation layout waited limit stored
  refine ⟨storage, run, fuel, finish, found, ?_, measured, lower, upper⟩
  exact sampledStored_storage_transport stored before waited storage storage run found found rfl (by intros; rfl) sampled


theorem waiting_value_backing (layout : LayoutEnv) (before : ExecutionState) (incoming : Nat)
    (value : Value) (backed : ValueStorageBacked layout before value) :
    ValueStorageBacked layout { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting incoming) } } value := by
  exact appended_ticket_value_backing layout before (.waiting incoming) value backed

theorem waiting_stored_observation (layout : LayoutEnv) (before : ExecutionState) (incoming : Nat)
    (limit : Nat → Nat) (stored : StoredValue) (observed : StoredBackingObservation layout before limit stored) :
    StoredBackingObservation layout { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting incoming) } } limit stored := by
  exact appended_ticket_stored_observation layout before (.waiting incoming) limit stored observed

theorem waitExitDestination_acceptedWorld (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (incoming : Nat)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (history : ReservationReferencesBounded before.construction ambient) :
    let token := before.construction.exitReservations.size
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting incoming) } }
    waitExitDestination incoming before.construction = .ok token waited.construction ∧
    AcceptedWorld config initialized waited (.completionChannels [token] [] [] :: ambient) types live regions pending := by
  let token := before.construction.exitReservations.size
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting incoming) } }
  have ownership := waitExitDestination_context before incoming ambient world.ownership history
  have execution := wait_completion_references_bounded before.construction ambient incoming [] [] history
  refine ⟨execution.1, ⟨⟨ownership, world.globals, world.globalTypes, world.layouts, world.typeFrontier,
    world.syntheticFrontier, world.heap, world.objectsRegistered, world.ordinalsRegistered, ?_, ?_, ?_⟩, world.globalLive⟩⟩
  · refine ⟨?_, world.backing.identities⟩
    intro root kept value found
    exact waiting_value_backing config.layout before incoming value (world.backing.values root kept value found)
  · intro region member
    have protection := world.protections region member
    refine ⟨protection.present, ?_, protection.cutoff, protection.landing, protection.authority,
      protection.authorityBound, protection.names⟩
    refine ⟨⟨?_, protection.observations.backing.identities⟩, ?_⟩
    · intro root kept value found
      exact waiting_value_backing config.layout before incoming value (protection.observations.backing.values root kept value found)
    · intro root kept value found stored occurrence
      exact waiting_stored_observation config.layout before incoming region.limit stored
        (protection.observations.observations root kept value found stored occurrence)
  · intro frame member
    exact ⟨(waiting_pending_carrier_ready config initialized before ambient types live regions pending incoming world frame member).2,
      waiting_pending_carrier_backing config initialized before ambient types live regions pending incoming world frame member⟩

theorem checked_numeric_operands_after_wait (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (source : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (incoming : Nat) (operands : List (CheckedNumericOperand source))
    (world : AcceptedWorld config source.initialized before ambient types live regions pending)
    (frame : AcceptedFrame config accepted source before types) (history : EvaluationHistoryCoverage before ambient pending) :
    let token := before.construction.exitReservations.size
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting incoming) } }
    let channels := operands.map (fun operand => Channel.register operand.ty)
    let expressions := operands.map CheckedNumericOperand.expression
    let outcome := evalOperands fuel config source.interpretation.environment channels expressions waited
    waitExitDestination incoming before.construction = .ok token waited.construction ∧
    EvaluationHistoryLifecycleOutcome .carriers channels (.completionChannels [token] [] [] :: ambient) pending outcome ∧
    Goose.Proofs.Exit.stepState outcome = waited ∧
    AcceptedWorld config source.initialized (Goose.Proofs.Exit.stepState outcome)
      (.completionChannels [token] [] [] :: ambient) types live regions pending ∧
    AcceptedFrame config accepted source (Goose.Proofs.Exit.stepState outcome) types ∧
    ∀ carriers after, outcome = .ok carriers after → after = waited ∧
      CarriersLandingReady after channels carriers ∧
      (∀ carrier ∈ carriers, CarrierResultBacking config.layout after carrier) ∧
      landCarriersInto 0 channels carriers after = .ok () after := by
  let token := before.construction.exitReservations.size
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting incoming) } }
  have waitedWorld := waitExitDestination_acceptedWorld config source.initialized before ambient types live regions pending incoming world history.1
  have waitedFrame := acceptedFrame_waitExitDestination incoming frame
  have waitHistory := wait_completion_references_bounded before.construction ambient incoming [] [] history.1
  have coverage : EvaluationHistoryCoverage waited (.completionChannels [token] [] [] :: ambient) pending := by
    refine ⟨waitHistory.2, ?_⟩
    intro id member
    simp only [OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers, List.nil_append] at member
    exact history.2 id member
  exact ⟨waitedWorld.1, checked_numeric_operands fuel config accepted source waited _ types live regions pending
    waitedWorld.2 waitedFrame.2 coverage operands⟩

#print axioms checked_numeric_operands_after_wait

#print axioms appended_ticket_value_backing
#print axioms appended_ticket_stored_observation
#print axioms waitExitDestination_acceptedWorld

end Goose.Proofs.ConstructionAcceptedExecution
