import Goose.Proofs.ConstructionExitByteWritePrefix
import Goose.Proofs.ConstructionAcceptedByteBacking

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem byte_writeLoop_storage_prefix (bytes : List UInt8) (layout : LayoutEnv)
    (origin : Goose.Core.OriginId) (id count : Nat) (before after : ExecutionState)
    (limit : Nat → Nat) (ready : OpenDestinationBacking layout before id (.varr (.int .u8)) count)
    (cutoff : limit ready.destination.storage ≤ ready.destination.capability.start)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) before = .ok PUnit.unit after) :
    StoragePrefixesEqual limit before.construction.storage after.construction.storage := by
  induction bytes generalizing before count with
  | nil =>
    simp only [List.forIn_nil, pure, ExecutionStep.ok.injEq, true_and] at executed
    subst after
    intro selected
    rfl
  | cons byte rest ih =>
    have renewal : renewReceivingDestination id before.construction = .ok id before.construction := by
      simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
        lookupDestination_result, ready.present, ready.opened]
    simp only [List.forIn_cons, receivingAction, liftConstruction, renewal, bind] at executed
    cases written : writeElement id ⟨#[byte]⟩ before.construction with
    | fault reason final => simp only [written] at executed; cases executed
    | ok value final =>
      cases value
      simp only [written, pure] at executed
      have element : ready.element = .int .u8 := by
        simpa only [elementType, Option.some.injEq] using ready.elementType.symm
      have encoded : ∃ fuel, packedEnd fuel layout ready.element ⟨#[byte]⟩ 0 = .ok (⟨#[byte]⟩ : ByteArray).size := by
        refine ⟨1, ?_⟩
        rw [element]
        rfl
      obtain ⟨next⟩ := writeElement_open_backing layout before final id (.varr (.int .u8)) count
        ⟨#[byte]⟩ ready encoded written
      have destination := writeElement_success_destination id ⟨#[byte]⟩ before.construction final
        ready.destination count ready.present ready.opened written
      have same : next.destination = { ready.destination with progress := .open (count + 1), writeEnd := ready.destination.writeEnd + (⟨#[byte]⟩ : ByteArray).size } :=
        Option.some.inj (next.present.symm.trans destination.1)
      have nextCutoff : limit next.destination.storage ≤ next.destination.capability.start := by
        rw [same]
        exact cutoff
      have indexing := writeElement_preserves_indexing id ⟨#[byte]⟩ before.construction
      rw [written] at indexing
      simp only [ConstructionResult.finalState] at indexing
      have current' : destinationCurrent final id = .ok id := by
        rw [destinationCurrent_result, destinationCurrentSteps_same_indexing _ before.construction final indexing.1 indexing.2, indexing.1]
        simpa only [destinationCurrent_result] using current
      have first := backed_byte_write_storage_prefix layout before final id count ⟨#[byte]⟩ limit ready cutoff written
      have remaining := ih (count + 1) { before with construction := final } next nextCutoff current' executed
      intro selected
      exact (remaining selected).trans (first selected)

#print axioms byte_writeLoop_storage_prefix

end Goose.Proofs.ConstructionAcceptedExecution
