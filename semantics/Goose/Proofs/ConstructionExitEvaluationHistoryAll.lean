import Goose.Proofs.ConstructionExitNamedMaterializationHistory
import Goose.Proofs.ConstructionExitEvaluationHistoryOwner
import Goose.Proofs.ConstructionExecutionProtocol

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

def TicketFloorLifecycle (floor : Nat) (state : ConstructionState) : Prop :=
  ReservationLifecycleInvariant state ∧ floor ≤ state.exitReservations.size

theorem preservation_implies_ticket_growth (action : ConstructionM α)
    (preserves : ∀ ambient pending, PreservesEvaluationHistoryLifecycle (liftConstruction 0 action) ambient pending)
    (state : ConstructionState) (valid : ReservationLifecycleInvariant state) :
    state.exitReservations.size ≤ (action state).finalState.exitReservations.size := by
  cases size : state.exitReservations.size with
  | zero => simp [size]
  | succ n =>
    let frame : OwnershipAmbientFrame := .exitChannels [n] [] []
    let initial := { ExecutionState.initial with construction := state }
    have history : EvaluationHistoryCoverage initial [frame] [] := by
      constructor
      · intro found member
        simp only [List.mem_singleton] at member
        subst found
        simp only [frame, OwnershipAmbientFrame.tickets, List.mem_singleton, forall_eq]
        constructor
        · change n < state.exitReservations.size
          omega
        · trivial
      · intro id member
        simp [OwnershipAmbient.retained, frame, OwnershipAmbientFrame.carriers] at member
    have result := preserves [frame] [] initial ⟨valid, history⟩
    have bound := (result.2.1 frame (by simp)).1 n (by simp [frame, OwnershipAmbientFrame.tickets])
    cases executed : action state with
    | ok value final =>
      simp only [initial, liftConstruction, executed, Goose.Proofs.Exit.stepState] at bound
      change n < final.exitReservations.size at bound
      simp only [executed, ConstructionResult.finalState, size]
      omega
    | fault kind final =>
      cases kind <;>
        simp only [initial, liftConstruction, executed, Goose.Proofs.Exit.stepState] at bound <;>
        change n < final.exitReservations.size at bound <;>
        simp only [executed, ConstructionResult.finalState, size] <;> omega

def ticketFloorPrimitives (floor : Nat) : ConstructionProtocolPrimitives (TicketFloorLifecycle floor) where
  storageFrame := by
    intro state storage same valid
    exact ⟨reservationLifecyclePrimitives.storageFrame state storage same valid.1, valid.2⟩
  preserves := by
    intro α action primitive state valid
    have lifecycle := reservationLifecyclePrimitives.preserves action primitive state valid.1
    have frame := constructionPrimitive_reservation_frame action primitive state valid.1.1
    exact ⟨lifecycle, by rw [frame.tickets]; exact valid.2⟩

def ticketFloorReservations (floor : Nat) : ConstructionReservationPrimitives (TicketFloorLifecycle floor) where
  restoreOwner := by
    intro snapshot incoming carried state valid
    have lifecycle := reservationLifecycleReservationPrimitives.restoreOwner snapshot incoming carried state valid.1
    have tickets := restoreCompletedOwner_tickets snapshot incoming carried state
    exact ⟨lifecycle, by rw [tickets]; exact valid.2⟩
  preserves := by
    intro α action primitive state valid
    have lifecycle := reservationLifecycleReservationPrimitives.preserves action primitive state valid.1
    have preserved : ∀ ambient pending, PreservesEvaluationHistoryLifecycle (liftConstruction 0 action) ambient pending := by
      cases primitive with
      | reserveExitDestination incoming source => exact evaluationHistoryLifecycle_reserve 0 incoming source
      | waitExitDestination incoming => exact evaluationHistoryLifecycle_wait 0 incoming
      | selectWaitingExitDestination token source => exact evaluationHistoryLifecycle_select_waiting 0 token source
      | rearmExitReservation borrowed => exact evaluationHistoryLifecycle_rearm 0 borrowed
      | markNamedReservation token => exact evaluationHistoryLifecycle_mark_named 0 token
      | materializeNamedReservation token => exact evaluationHistoryLifecycle_materialize_named 0 token
      | renewReceivingDestination incoming => exact evaluationHistoryLifecycle_renew 0 incoming
      | releaseExitReservation token => exact evaluationHistoryLifecycle_release 0 token
      | cancelExitReservation token carried => exact evaluationHistoryLifecycle_cancel 0 token carried
      | landExitReplacementChain id => exact evaluationHistoryLifecycle_land_chain 0 id
      | landExitReplacementInto receiving id => exact evaluationHistoryLifecycle_land_into 0 receiving id
    exact ⟨lifecycle, Nat.le_trans valid.2 (preservation_implies_ticket_growth action preserved state valid.1)⟩

theorem evaluator_ticket_floor (fuel : Nat) (config : EvalConfig) (shape : OwnershipResultShape α)
    (action : EvalM α) (actual : OwnershipEvaluationAction fuel config shape action)
    (state : ExecutionState) (valid : ReservationLifecycleInvariant state.construction) :
    TicketFloorLifecycle state.construction.exitReservations.size (Goose.Proofs.Exit.stepState (action state)).construction := by
  letI := ticketFloorPrimitives state.construction.exitReservations.size
  letI := ticketFloorReservations state.construction.exitReservations.size
  have family := evaluation_preservesConstructionInvariant (predicate := TicketFloorLifecycle state.construction.exitReservations.size) fuel config
  have initial : ExecutionInvariant (TicketFloorLifecycle state.construction.exitReservations.size) state := ⟨valid, Nat.le_refl _⟩
  cases actual with
  | value environment expression => exact family.value environment expression state initial
  | bound environment count defaultValue operand => exact family.bound environment count defaultValue operand state initial
  | place environment operand => exact family.place environment operand state initial
  | view environment operand => exact family.view environment operand state initial
  | produce environment channels operand => exact family.produce environment channels operand state initial
  | operands environment channels expressions => exact family.operands environment channels expressions state initial
  | build environment destination expression => exact family.build environment destination expression state initial
  | element environment destination element expression => exact family.element environment destination element expression state initial
  | arguments environment vars params args => exact family.arguments environment vars params args state initial
  | call environment context args channels origin => exact family.call environment context args channels origin state initial
  | activation environment pre body origin => exact family.activation environment pre body origin state initial
  | activationBody environment pre body => exact family.activationBody environment pre body state initial
  | resultBlock environment channels body => exact family.resultBlock environment channels body state initial
  | resultBlockWith environment pre channels body => exact family.resultBlockWith environment pre channels body state initial
  | block environment pre channels body => exact family.block environment pre channels body state initial
  | statements environment statements => exact family.statements environment statements state initial
  | statement environment statement => exact family.statement environment statement state initial
  | printArgument environment argument => exact family.printArgument environment argument state initial
  | whileLoop environment condition body => exact family.whileLoop environment condition body state initial
  | rangeLoop environment var ty first last body => exact family.rangeLoop environment var ty first last body state initial
  | eachLoop environment var index byRef body view current => exact family.eachLoop environment var index byRef body view current state initial
  | loop environment pre body => exact family.loop environment pre body state initial
  | push environment owner expression origin => exact family.push environment owner expression origin state initial

theorem evaluator_fixed_history_coverage (fuel : Nat) (config : EvalConfig) (shape : OwnershipResultShape α)
    (action : EvalM α) (actual : OwnershipEvaluationAction fuel config shape action)
    (state : ExecutionState) (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame)
    (valid : EvaluationHistoryLifecycle state ambient pending) :
    EvaluationHistoryLifecycle (Goose.Proofs.Exit.stepState (action state)) ambient pending := by
  have floor := evaluator_ticket_floor fuel config shape action actual state valid.1
  exact ⟨floor.1, reservationReferencesBounded_mono state.construction _ ambient floor.2 valid.2.1, valid.2.2⟩

theorem runModule_fixed_history_coverage (fuel : Nat) (config : EvalConfig)
    (state : ExecutionState) (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame)
    (valid : EvaluationHistoryLifecycle state ambient pending) :
    EvaluationHistoryLifecycle (Goose.Proofs.Exit.stepState (runModule fuel config state)) ambient pending := by
  letI := ticketFloorPrimitives state.construction.exitReservations.size
  letI := ticketFloorReservations state.construction.exitReservations.size
  have floor := runModule_preservesConstructionInvariant
    (predicate := TicketFloorLifecycle state.construction.exitReservations.size) fuel config state ⟨valid.1, Nat.le_refl _⟩
  exact ⟨floor.1, reservationReferencesBounded_mono state.construction _ ambient floor.2 valid.2.1, valid.2.2⟩

#print axioms runModule_fixed_history_coverage
#print axioms preservation_implies_ticket_growth
#print axioms evaluator_ticket_floor
#print axioms evaluator_fixed_history_coverage

end Goose.Proofs.ConstructionAcceptedExecution
