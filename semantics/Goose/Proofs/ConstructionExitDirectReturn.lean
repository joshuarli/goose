import Goose.Proofs.ConstructionExitDirectSourceRoles
import Goose.Proofs.ConstructionExitSingleCleanup
import Goose.Proofs.ConstructionExitByteProduce
import Goose.Proofs.ConstructionExitByteAdaptation
import Goose.Proofs.ConstructionExitByteFinishPrefix

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem direct_byte_return_cleanup (fuel : Nat) (config : EvalConfig)
    (source target : RuntimeActivation) (targetId id : Nat) (bytes : List UInt8) (origin : OriginId)
    (initial : ExecutionState) (ready : OpenDestinationBacking config.layout initial id (.varr (.int .u8)) 0)
    (ownership : OwnershipSourceState initial.construction)
    (selection : targetActivation config targetId initial = .ok target initial)
    (channels : target.channels = [.construct id])
    (receiver : ready.destination.use = .receiver) (packed : ready.destination.layout = .packed)
    (adaptation : ready.destination.adaptation = none)
    (physical : ready.destination.capability.layout = .varr (.int .u8)) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent initial.construction id = .ok id) (fits : bytes.length < 2 ^ 32) :
    ∃ after : ExecutionState,
      let token := initial.construction.exitReservations.size
      let cleaned := { after with construction := { after.construction with
        exitReservations := after.construction.exitReservations.set! token .released } }
      execStmt (fuel + 4) config source (.returnFrom targetId [.bytes (.varr (.int .u8)) bytes origin] origin) initial =
        .escape ⟨target.act, .nonlocal targetId⟩ [.completed id] cleaned ∧
      landCarriersInto origin [.construct id] [.completed id] cleaned = .ok () cleaned ∧
      finishChannels config.layout [.construct id] [.varr (.int .u8)] [.completed id] origin cleaned = .ok () cleaned ∧
      LandedResultChannels cleaned [.construct id] [.varr (.int .u8)] [.completed id] ∧
      ∀ limit, limit ready.destination.storage ≤ ready.destination.capability.start →
        StoragePrefixesEqual limit initial.construction.storage after.construction.storage := by
  let token := initial.construction.exitReservations.size
  let reserved := { initial.construction with exitReservations := initial.construction.exitReservations.push (.active .fresh id id ready.destination) }
  let prepared := { initial with construction := reserved }
  let preparedReady : OpenDestinationBacking config.layout prepared id (.varr (.int .u8)) 0 :=
    { ready with present := ready.present, bytes := ready.bytes }
  have preparedSource : OwnershipSourceState reserved :=
    direct_fresh_source_state initial.construction id ready.destination ownership ready.present ready.opened current
  have preparedCurrent : destinationCurrent reserved id = .ok id := by
    rw [destinationCurrent_congr_tables initial.construction reserved rfl rfl id]
    exact current
  obtain ⟨after, built⟩ := packed_receiver_byte_build fuel config source bytes origin prepared id 0
    ready.destination ready.storage ready.present ready.bytes ready.opened packed adaptation receiver request preparedCurrent (by simpa using fits)
  have afterSource := buildExpr_bytes_sourceState fuel config source id (.varr (.int .u8)) bytes origin
    prepared after ready.destination 0 preparedSource preparedCurrent ready.present ready.opened built
  obtain ⟨destination, storage, found, _, _, _, _, _, use, progress, _⟩ :=
    buildExpr_byteOwner_geometry fuel config source bytes origin id 0 prepared after preparedReady packed request
      (by simpa using fits) preparedSource.structural.1.1.1 preparedCurrent built
  have terminal := destinationSuccessorKeysInactive_built_terminal after.construction afterSource.inactiveKeys
    id destination found (0 + bytes.length) progress
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have resolved : destinationCurrent after.construction id = .ok id := by
    simp only [destinationCurrent_result, destinationCurrentSteps_succ, inside, ↓reduceIte, terminal]
  have reservedFound : reserved.destinations[id]? = some ready.destination := ready.present
  have renewal : renewReceivingDestination id prepared.construction = .ok id prepared.construction := by
    change renewReceivingDestination id reserved = .ok id reserved
    simp only [renewReceivingDestination, ConstructionM.get, bind, preparedCurrent, pure,
      lookupDestination_result, reservedFound, ready.opened]
  have complete : completedReceivingDestination id after = .ok id after := by
    simp only [completedReceivingDestination, receivingDestination, liftConstruction, resolved,
      bind, completedDestination, getDestination, EvalM.get, found, progress, pure]
  have produced : evalProduce (fuel + 2) config source [.construct id] (.bytes (.varr (.int .u8)) bytes origin) prepared =
      .ok [.completed id] after := by
    simp only [evalProduce, List.mapM_cons, List.mapM_nil, liftConstruction, renewal, bind, pure,
      selectCompletionChannel, built, complete]
  have evaluated : evalOperands (fuel + 3) config source [.construct id] [.bytes (.varr (.int .u8)) bytes origin] prepared =
      .ok [.completed id] after := by
    simp only [evalOperands, produced, bind, singleCarrier, pure]
  have setup := direct_byte_exit_setup source target bytes origin initial id ready.destination channels ready.present ready.opened current
  have tickets := buildExpr_bytes_tickets fuel config source id (.varr (.int .u8)) bytes origin prepared after
    ready.destination 0 preparedSource preparedCurrent ready.present ready.opened built
  have ticket : after.construction.exitReservations[token]? = some (.active .fresh id id ready.destination) := by
    rw [tickets]
    exact setup.2.2
  have escaped := returnFrom_single_completed_cleanup (fuel + 3) config source target targetId
    (.bytes (.varr (.int .u8)) bytes origin) origin initial prepared after id token id ready.destination
    selection setup.1 setup.2.1 evaluated ticket
  have cleanCurrent : destinationCurrent { after.construction with exitReservations := after.construction.exitReservations.set! token .released } id = .ok id := by
    have same := destinationCurrent_congr_tables after.construction
      { after.construction with exitReservations := after.construction.exitReservations.set! token .released } rfl rfl id
    exact same.trans resolved
  dsimp only [token] at cleanCurrent
  refine ⟨after, escaped.1, ?_, ?_, ?_, ?_⟩
  · simp only [landCarriersInto, List.length_cons, List.length_nil, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons,
      List.forIn_nil, receivingDestination, liftConstruction, cleanCurrent, bind, pure]
  · obtain ⟨capRow, capFound, capEq, _⟩ := build_packed_bytes_capability fuel config source id 0 bytes origin
      prepared after preparedSource preparedReady packed request preparedCurrent built
    obtain ⟨adaptRow, adaptFound, adaptEq, _⟩ := build_packed_bytes_adaptation fuel config source id 0 bytes origin
      prepared after preparedSource preparedReady packed request preparedCurrent built
    have capSame : capRow = destination := Option.some.inj (capFound.symm.trans found)
    have adaptSame : adaptRow = destination := Option.some.inj (adaptFound.symm.trans found)
    subst capRow
    subst adaptRow
    have finalAdaptation : destination.adaptation = none := adaptEq.trans adaptation
    have finalPhysical : destination.capability.layout = .varr (.int .u8) := by rw [capEq]; exact physical
    have finalLogical : destination.capability.logicalType = .varr (.int .u8) := by rw [capEq]; exact ready.logicalType
    let cleaned := { after with construction := { after.construction with
      exitReservations := after.construction.exitReservations.set! token .released } }
    have finish := byte_receiver_finishChannel config.layout origin cleaned id (0 + bytes.length) destination
      found progress (use.trans receiver) finalAdaptation finalPhysical finalLogical
    have land : landCarriersInto origin [.construct id] [.completed id] cleaned = .ok () cleaned := by
      simp only [landCarriersInto, List.length_cons, List.length_nil, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons,
        List.forIn_nil, receivingDestination, liftConstruction, cleanCurrent, bind, pure, cleaned, token]
    change finishChannels config.layout [.construct id] [.varr (.int .u8)] [.completed id] origin cleaned = .ok () cleaned
    simp only [finishChannels, land, bind, List.length_cons, List.length_nil, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons,
      List.forIn_nil, finish, pure]
  · obtain ⟨capRow, capFound, capEq, _⟩ := build_packed_bytes_capability fuel config source id 0 bytes origin
      prepared after preparedSource preparedReady packed request preparedCurrent built
    obtain ⟨adaptRow, adaptFound, adaptEq, _⟩ := build_packed_bytes_adaptation fuel config source id 0 bytes origin
      prepared after preparedSource preparedReady packed request preparedCurrent built
    have capSame : capRow = destination := Option.some.inj (capFound.symm.trans found)
    have adaptSame : adaptRow = destination := Option.some.inj (adaptFound.symm.trans found)
    subst capRow
    subst adaptRow
    have finalAdaptation : destination.adaptation = none := adaptEq.trans adaptation
    have finalPhysical : destination.capability.layout = .varr (.int .u8) := by rw [capEq]; exact physical
    have finalLogical : destination.capability.logicalType = .varr (.int .u8) := by rw [capEq]; exact ready.logicalType
    let cleaned := { after with construction := { after.construction with
      exitReservations := after.construction.exitReservations.set! token .released } }
    have normalized : NormalizedCompletedCarrier cleaned (.varr (.int .u8)) id :=
      ⟨destination, found, ⟨0 + bytes.length, progress⟩,
        receiver_destination_writable cleaned.construction id destination found (use.trans receiver),
        finalAdaptation, by simp only [finalPhysical, Bool.not_true, Bool.and_false], finalLogical, rfl⟩
    exact .cons (.construct id id _ cleanCurrent normalized) .nil
  · intro limit cutoff
    exact build_packed_byte_storage_prefix fuel config source id 0 bytes origin prepared after limit
      preparedSource preparedReady packed request cutoff preparedCurrent built

#print axioms direct_byte_return_cleanup

end Goose.Proofs.ConstructionAcceptedExecution
