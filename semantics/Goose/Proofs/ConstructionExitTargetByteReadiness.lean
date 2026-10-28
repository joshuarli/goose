import Goose.Proofs.ConstructionExitTargetRegisters
import Goose.Proofs.ConstructionExitDirectReturn
import Goose.Proofs.ConstructionExitStructuralRelease
import Goose.Proofs.ConstructionExitDirectHistory

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

theorem checked_byte_returnFrom_target (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (source target : RuntimeActivation) (targetId id : Nat) (bytes : List UInt8) (origin : OriginId)
    (initial : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized initial ambient types live regions pending)
    (history : EvaluationHistoryCoverage initial ambient pending)
    (ready : OpenDestinationBacking config.layout initial id (.varr (.int .u8)) 0)
    (selection : targetActivation config targetId initial = .ok target initial)
    (channels : target.channels = [.construct id])
    (receiver : ready.destination.use = .receiver) (packed : ready.destination.layout = .packed)
    (adaptation : ready.destination.adaptation = none) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent initial.construction id = .ok id) (fits : bytes.length < 2 ^ 32) :
    ∃ after : ExecutionState,
      let token := initial.construction.exitReservations.size
      let cleaned := { after with construction := { after.construction with
        exitReservations := after.construction.exitReservations.set! token .released } }
      execStmt (fuel + 4) config source (.returnFrom targetId [.bytes (.varr (.int .u8)) bytes origin] origin) initial =
        .escape ⟨target.act, .nonlocal targetId⟩ [.completed id] cleaned ∧
      CarriersLandingReady cleaned target.channels [.completed id] ∧
      CarrierResultBacking config.layout cleaned (.completed id) ∧
      landCarriersInto origin target.channels [.completed id] cleaned = .ok () cleaned ∧
      OwnershipSourceState cleaned.construction ∧
      EvaluationHistoryLifecycle cleaned (.returned [.completed id] :: ambient) (⟨target.channels, [.completed id]⟩ :: pending) := by
  let token := initial.construction.exitReservations.size
  let reserved := { initial.construction with exitReservations := initial.construction.exitReservations.push (.active .fresh id id ready.destination) }
  let prepared := { initial with construction := reserved }
  let preparedReady : OpenDestinationBacking config.layout prepared id (.varr (.int .u8)) 0 :=
    { ready with present := ready.present, bytes := ready.bytes }
  have sourceBefore := direct_fresh_source_state initial.construction id ready.destination world.ownership.source ready.present ready.opened current
  have resolvedBefore : destinationCurrent reserved id = .ok id := by
    rw [destinationCurrent_congr_tables initial.construction reserved rfl rfl id]
    exact current
  obtain ⟨after, built⟩ := packed_receiver_byte_build fuel config source bytes origin prepared id 0
    ready.destination ready.storage ready.present ready.bytes ready.opened packed adaptation receiver request resolvedBefore (by simpa using fits)
  have afterSource := buildExpr_bytes_sourceState fuel config source id (.varr (.int .u8)) bytes origin prepared after
    ready.destination 0 sourceBefore resolvedBefore ready.present ready.opened built
  obtain ⟨destination, storage, found, _, _, _, _, _, use, progress, _⟩ :=
    buildExpr_byteOwner_geometry fuel config source bytes origin id 0 prepared after preparedReady packed request
      (by simpa using fits) sourceBefore.structural.1.1.1 resolvedBefore built
  have terminal := destinationSuccessorKeysInactive_built_terminal after.construction afterSource.inactiveKeys id destination found
    (0 + bytes.length) progress
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have resolvedAfter : destinationCurrent after.construction id = .ok id := by
    simp only [destinationCurrent_result, destinationCurrentSteps_succ, inside, ↓reduceIte, terminal]
  have reservedFound : reserved.destinations[id]? = some ready.destination := ready.present
  have renewal : renewReceivingDestination id prepared.construction = .ok id prepared.construction := by
    change renewReceivingDestination id reserved = .ok id reserved
    simp only [renewReceivingDestination, ConstructionM.get, bind, resolvedBefore, pure,
      lookupDestination_result, reservedFound, ready.opened]
  have complete : completedReceivingDestination id after = .ok id after := by
    simp only [completedReceivingDestination, receivingDestination, liftConstruction, resolvedAfter,
      bind, completedDestination, getDestination, EvalM.get, found, progress, pure]
  have produced : evalProduce (fuel + 2) config source [.construct id] (.bytes (.varr (.int .u8)) bytes origin) prepared =
      .ok [.completed id] after := by
    simp only [evalProduce, List.mapM_cons, List.mapM_nil, liftConstruction, renewal, bind, pure,
      selectCompletionChannel, built, complete]
  have evaluated : evalOperands (fuel + 3) config source [.construct id] [.bytes (.varr (.int .u8)) bytes origin] prepared =
      .ok [.completed id] after := by simp only [evalOperands, produced, bind, singleCarrier, pure]
  have setup := direct_byte_exit_setup source target bytes origin initial id ready.destination channels ready.present ready.opened current
  have tickets := buildExpr_bytes_tickets fuel config source id (.varr (.int .u8)) bytes origin prepared after
    ready.destination 0 sourceBefore resolvedBefore ready.present ready.opened built
  have ticket : after.construction.exitReservations[token]? = some (.active .fresh id id ready.destination) := by
    rw [tickets]
    exact setup.2.2
  have escaped := returnFrom_single_completed_cleanup (fuel + 3) config source target targetId
    (.bytes (.varr (.int .u8)) bytes origin) origin initial prepared after id token id ready.destination
    selection setup.1 setup.2.1 evaluated ticket
  let cleaned := { after with construction := { after.construction with
    exitReservations := after.construction.exitReservations.set! token .released } }
  have cleanCurrent : destinationCurrent cleaned.construction id = .ok id := by
    rw [destinationCurrent_congr_tables after.construction cleaned.construction rfl rfl id]
    exact resolvedAfter
  have targetReady : ReceivingCarrierLandingReady cleaned id id :=
    ⟨id, destination, destination, cleanCurrent, found, found, .refl _, .receiver (use.trans receiver), Nat.le_refl _⟩
  obtain ⟨stored, sampled, storedBacking⟩ := buildExpr_byteOwner_backing fuel config source bytes origin id 0
    prepared after preparedReady packed request (by simpa using fits) sourceBefore.structural.1.1.1 resolvedBefore built
  have cleanStored : StoredValueBacking config.layout cleaned stored := by
    cases storedBacking with
    | detached storage element present detached type interval => exact .detached storage element present detached type interval
    | named namedId storage row count present named binding backing type start phase element elementType interval =>
      exact .named namedId storage row count present named binding backing type start phase element elementType interval
  have cleanFound : cleaned.construction.destinations[id]? = some destination := found
  have cleanSampled : storedDestination id cleaned = .ok stored cleaned := by
    simp only [storedDestination, getDestination, EvalM.get, bind, found, pure, progress, progressCount,
      ExecutionStep.ok.injEq, and_true] at sampled
    simp only [storedDestination, getDestination, EvalM.get, bind, cleanFound, pure, progress, progressCount,
      ExecutionStep.ok.injEq, and_true]
    exact sampled
  have cleanSource : OwnershipSourceState cleaned.construction :=
    ownershipSource_after_ticket_release after.construction token id id ready.destination ticket afterSource
  have tracked := evaluator_history_outcome (fuel + 4) config .none _
    (.statement source (.returnFrom targetId [.bytes (.varr (.int .u8)) bytes origin] origin)) initial ambient pending target.channels
    ⟨world.ownership.source.structural.1.1, history⟩
  have cleanedHistory : EvaluationHistoryLifecycle cleaned (.returned [.completed id] :: ambient)
      (⟨target.channels, [.completed id]⟩ :: pending) := by
    simpa only [escaped.1, EvaluationHistoryLifecycleOutcome] using tracked
  refine ⟨after, escaped.1, ?_, .completed id (0 + bytes.length) destination stored found progress cleanSampled cleanStored, ?_, cleanSource, cleanedHistory⟩
  · rw [channels]
    refine ⟨rfl, ?_⟩
    intro channel carrier member
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    exact .construct id id targetReady
  · rw [channels]
    dsimp only [cleaned, token] at cleanCurrent
    simp only [landCarriersInto, List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons, List.forIn_nil,
      receivingDestination, liftConstruction, cleanCurrent, bind, pure]

#print axioms checked_byte_returnFrom_target

end Goose.Proofs.ConstructionAcceptedExecution
