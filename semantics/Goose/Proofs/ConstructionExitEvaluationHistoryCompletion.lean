import Goose.Proofs.ConstructionExitEvaluationHistoryProduced
import Goose.Proofs.ConstructionExitDirectSourceRoles
import Goose.Proofs.ConstructionExitCompletionActivation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

private theorem push_waiting_selects_fresh {α : Type} (entries : Array α) (waiting active : α) :
    (entries.push waiting).set! entries.size active = entries.push active := by
  simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, Array.set_push]

theorem completion_byte_receiver_history (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (bytes : List UInt8) (origin : OriginId)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (history : EvaluationHistoryCoverage before ambient pending)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (receiver : ready.destination.use = .receiver) (packed : ready.destination.layout = .packed)
    (adaptation : ready.destination.adaptation = none) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32) :
    let token := before.construction.exitReservations.size
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting id) } }
    let frame : PendingCarrierFrame := ⟨[.completion token], [.completed id]⟩
    ∃ after : ExecutionState,
      waitExitDestination id before.construction = .ok token waited.construction ∧
      evalProduce (fuel + 2) config environment frame.channels (.bytes (.varr (.int .u8)) bytes origin) waited =
        .ok frame.carriers after ∧
      EvaluationHistoryCoverage after (.returned frame.carriers :: .completionChannels [token] [] [] :: ambient) (frame :: pending) ∧
      CarriersLandingReady after frame.channels frame.carriers ∧
      (∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout after carrier) ∧
      landCarriersInto origin frame.channels frame.carriers after = .ok () after := by
  let token := before.construction.exitReservations.size
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting id) } }
  let reserved := { before.construction with exitReservations := before.construction.exitReservations.push (.active .fresh id id ready.destination) }
  let prepared := { before with construction := reserved }
  let preparedReady : OpenDestinationBacking config.layout prepared id (.varr (.int .u8)) 0 :=
    { ready with present := ready.present, bytes := ready.bytes }
  have selection := wait_then_select_completion_open_byte before environment id ready.destination (.varr (.int .u8)) bytes origin
    ready.present ready.opened current
  have selected : selectCompletionChannel environment (.bytes (.varr (.int .u8)) bytes origin) (.completion token) waited =
      .ok (.construct id) prepared := by
    simpa only [token, waited, prepared, reserved, push_waiting_selects_fresh] using selection.2
  have source := direct_fresh_source_state before.construction id ready.destination world.ownership.source ready.present ready.opened current
  have resolvedBefore : destinationCurrent reserved id = .ok id := by
    rw [destinationCurrent_congr_tables before.construction reserved rfl rfl id]
    exact current
  obtain ⟨after, built⟩ := packed_receiver_byte_build fuel config environment bytes origin prepared id 0
    ready.destination ready.storage ready.present ready.bytes ready.opened packed adaptation receiver request resolvedBefore (by simpa using fits)
  have sourceAfter := buildExpr_bytes_sourceState fuel config environment id (.varr (.int .u8)) bytes origin
    prepared after ready.destination 0 source resolvedBefore ready.present ready.opened built
  obtain ⟨destination, storage, found, _, _, _, _, _, use, progress, _⟩ :=
    buildExpr_byteOwner_geometry fuel config environment bytes origin id 0 prepared after preparedReady packed request
      (by simpa using fits) source.structural.1.1.1 resolvedBefore built
  have terminal := destinationSuccessorKeysInactive_built_terminal after.construction sourceAfter.inactiveKeys
    id destination found (0 + bytes.length) progress
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have resolvedAfter : destinationCurrent after.construction id = .ok id := by
    simp only [destinationCurrent_result, destinationCurrentSteps_succ, inside, ↓reduceIte, terminal]
  have completed : completedReceivingDestination id after = .ok id after := by
    simp only [completedReceivingDestination, receivingDestination, liftConstruction, resolvedAfter,
      bind, completedDestination, getDestination, EvalM.get, found, progress, pure]
  have tickets := buildExpr_bytes_tickets fuel config environment id (.varr (.int .u8)) bytes origin prepared after
    ready.destination 0 source resolvedBefore ready.present ready.opened built
  have ticket : after.construction.exitReservations[token]? = some (.active .fresh id id ready.destination) := by
    rw [tickets]
    simp [prepared, reserved, token]
  have byteReady : ReceivingCarrierLandingReady after id id :=
    ⟨id, destination, destination, resolvedAfter, found, found, .refl _, .receiver (use.trans receiver), Nat.le_refl _⟩
  obtain ⟨stored, sampled, valueBacking⟩ := buildExpr_byteOwner_backing fuel config environment bytes origin id 0
    prepared after preparedReady packed request (by simpa using fits) source.structural.1.1.1 resolvedBefore built
  have backed : CarrierResultBacking config.layout after (.completed id) :=
    .completed id (0 + bytes.length) destination stored found progress sampled valueBacking
  have evaluated : evalProduce (fuel + 2) config environment [.completion token] (.bytes (.varr (.int .u8)) bytes origin) waited =
      .ok [.completed id] after := by
    simp only [evalProduce, List.mapM_cons, List.mapM_nil, bind, pure, selected, built, completed]
  have waitingHistory := wait_completion_references_bounded before.construction ambient id [] [] history.1
  have bounded : ReservationReferencesBounded after.construction (.completionChannels [token] [] [] :: ambient) := by
    apply reservationReferencesBounded_mono waited.construction after.construction _ _ waitingHistory.2
    simp only [tickets, prepared, reserved, waited, Array.size_push, Array.size_set!]
    exact Nat.le_refl _
  have prior : EvaluationHistoryCoverage after (.completionChannels [token] [] [] :: ambient) pending := by
    refine ⟨bounded, ?_⟩
    intro old member
    simp only [OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers, List.nil_append] at member
    exact history.2 old member
  refine ⟨after, selection.1, evaluated, evaluationHistoryCoverage_returned after _ pending [.completion token] [.completed id] prior, ?_, ?_, ?_⟩
  · refine ⟨rfl, ?_⟩
    intro channel carrier member
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    exact .completion token id id id .fresh ready.destination ticket byteReady
  · intro carrier member
    simp only [List.mem_singleton] at member
    subst carrier
    exact backed
  · dsimp only [token] at ticket
    simp only [landCarriersInto, List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons, List.forIn_nil, EvalM.get, bind, ticket,
      receivingDestination, liftConstruction, resolvedAfter, pure]

#print axioms completion_byte_receiver_history

end Goose.Proofs.ConstructionAcceptedExecution
