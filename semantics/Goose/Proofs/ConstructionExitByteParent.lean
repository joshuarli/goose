import Goose.Proofs.ConstructionExitByteReservation
import Goose.Proofs.ConstructionExitOpenReservation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ExitExecution

theorem bytes_writeLoop_other_row (bytes : List UInt8) (origin : Goose.Core.OriginId) (id : Nat)
    (before after : ExecutionState) (row : PendingDestination) (count : Nat) (other : Nat) (different : other ≠ id)
    (valid : OwnershipSourceState before.construction)
    (current : destinationCurrent before.construction id = .ok id)
    (present : before.construction.destinations[id]? = some row) (opened : row.progress = .open count)
    (executed : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) before = .ok PUnit.unit after) :
    after.construction.destinations[other]? = before.construction.destinations[other]? := by
  induction bytes generalizing before row count with
  | nil => simp only [List.forIn_nil, pure, ExecutionStep.ok.injEq, true_and] at executed; subst after; rfl
  | cons byte rest ih =>
    have renewal : renewReceivingDestination id before.construction = .ok id before.construction := by
      simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
        lookupDestination_result, present, opened]
    simp only [List.forIn_cons, receivingAction, liftConstruction, renewal, bind] at executed
    cases written : writeElement id ⟨#[byte]⟩ before.construction with
    | fault reason final => simp only [written] at executed; cases executed
    | ok value final =>
      cases value
      simp only [written, pure] at executed
      have transition := writeElement_transition id ⟨#[byte]⟩ before.construction
      rw [written] at transition
      have frame : final.destinations[other]? = before.construction.destinations[other]? := by
        cases transition with
        | written actual storage count found stored opened =>
          simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Ne.symm different]
      have extension := writeElement_ownership_source id ⟨#[byte]⟩ before.construction valid.structural.1.1.1
      have nextValid := constructionPrimitive_sourceState_of_sourceExtension (writeElement id ⟨#[byte]⟩)
        (.writeElement id ⟨#[byte]⟩) before.construction valid extension
      rw [written] at nextValid
      have row' := writeElement_success_destination id ⟨#[byte]⟩ before.construction final row count present opened written
      have indexing := writeElement_preserves_indexing id ⟨#[byte]⟩ before.construction
      rw [written] at indexing
      simp only [ConstructionResult.finalState] at indexing
      have current' : destinationCurrent final id = .ok id := by
        rw [destinationCurrent_result, destinationCurrentSteps_same_indexing _ before.construction final indexing.1 indexing.2, indexing.1]
        simpa only [destinationCurrent_result] using current
      have next := ih { before with construction := final }
        { row with progress := .open (count + 1), writeEnd := row.writeEnd + (⟨#[byte]⟩ : ByteArray).size } (count + 1)
        nextValid current' row'.1 rfl executed
      exact next.trans frame

theorem reserved_parent_survives_byte_writes (reservationBefore reserved : ConstructionState)
    (incoming selected token count writeCount : Nat) (original selectedRow : PendingDestination)
    (present : reservationBefore.destinations[incoming]? = some original)
    (opened : original.progress = .open (count + 1))
    (receiverCurrent : destinationCurrent reservationBefore incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue reservationBefore = .ok (token, selected) reserved)
    (before after : ExecutionState) (construction : before.construction = reserved)
    (valid : OwnershipSourceState before.construction)
    (selectedCurrent : destinationCurrent before.construction selected = .ok selected)
    (selectedPresent : before.construction.destinations[selected]? = some selectedRow)
    (selectedOpen : selectedRow.progress = .open writeCount)
    (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (writes : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin selected (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) before = .ok PUnit.unit after)
    (environment : RuntimeActivation) (scope : Nat) (scopeInst : Goose.Core.ScopeInst) :
    (releaseScopeState environment scope scopeInst after).construction.destinations[incoming]? =
      some { original with progress := .exiting (count + 1) selected } := by
  have parent := (reserve_open_receiver_snapshot reservationBefore reserved incoming selected token count original
    present opened receiverCurrent reservation).1
  have distinct : incoming ≠ selected := by
    intro equal
    have same : { original with progress := .exiting (count + 1) selected } = selectedRow := by
      apply Option.some.inj
      rw [← construction] at parent
      rw [equal] at parent
      exact parent.symm.trans selectedPresent
    have impossible := congrArg PendingDestination.progress same
    simp only [selectedOpen] at impossible
    cases impossible
  have unchanged := bytes_writeLoop_other_row bytes origin selected before after selectedRow writeCount incoming distinct
    valid selectedCurrent selectedPresent selectedOpen writes
  simpa only [releaseScopeState, unchanged, construction] using parent

#print axioms reserved_parent_survives_byte_writes
#print axioms bytes_writeLoop_other_row

end Goose.Proofs.ConstructionAcceptedExecution
