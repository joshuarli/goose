import Goose.Proofs.ConstructionExitSnapshotNoChildren
import Goose.Proofs.ConstructionExitChildWrite

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionStorage

theorem bytes_writeLoop_child_invariants (bytes : List UInt8) (origin : OriginId) (id : Nat)
    (before after : ExecutionState) (row : PendingDestination) (count : Nat)
    (valid : OwnershipSourceState before.construction)
    (current : destinationCurrent before.construction id = .ok id)
    (present : before.construction.destinations[id]? = some row) (opened : row.progress = .open count)
    (unique : ActiveChildUnique before.construction) (blocked : ActiveChildParentBlocked before.construction)
    (executed : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) before = .ok PUnit.unit after) :
    ActiveChildUnique after.construction ∧ ActiveChildParentBlocked after.construction := by
  induction bytes generalizing before row count with
  | nil =>
    simp only [List.forIn_nil, pure, ExecutionStep.ok.injEq, true_and] at executed
    subst after
    exact ⟨unique, blocked⟩
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
      have nextCandidates := writeElement_preserves_child_invariants before.construction final id ⟨#[byte]⟩ unique blocked written
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
      exact ih { before with construction := final }
        { row with progress := .open (count + 1), writeEnd := row.writeEnd + (⟨#[byte]⟩ : ByteArray).size } (count + 1)
        nextValid current' row'.1 rfl nextCandidates.1 nextCandidates.2 executed

theorem build_packed_bytes_child_invariants (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id count : Nat) (bytes : List UInt8) (origin : OriginId) (before after : ExecutionState)
    (valid : OwnershipSourceState before.construction)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id)
    (unique : ActiveChildUnique before.construction) (blocked : ActiveChildParentBlocked before.construction)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    ActiveChildUnique after.construction ∧ ActiveChildParentBlocked after.construction := by
  have renewal : renewReceivingDestination id before.construction = .ok id before.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, ready.present, ready.opened]
  simp only [buildExpr, liftConstruction, renewal, bind] at executed
  have action := protectDestination_success origin id _ before after () executed
  cases loop : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) before with
  | stop reason state => simp only [bind] at loop; rw [loop] at action; cases action
  | escape target carriers state => simp only [bind] at loop; rw [loop] at action; cases action
  | jump target kind state => simp only [bind] at loop; rw [loop] at action; cases action
  | ok value middle =>
    cases value
    have candidates := bytes_writeLoop_child_invariants bytes origin id before middle ready.destination count valid current
      ready.present ready.opened unique blocked loop
    obtain ⟨source, lifecycle, current', next, n, present', opened'⟩ :=
      bytes_writeLoop_ownershipSource bytes origin id before middle ready.destination count valid.structural.1.1.1 current ready.present ready.opened loop
    obtain ⟨following, sameLayout, sameCapability, _, _⟩ :=
      bytes_writeLoop_open_backing bytes config.layout origin id count before middle ready current loop
    have same : next = following.destination := Option.some.inj (present'.symm.trans following.present)
    have packed' : next.layout = .packed := by rw [same, sameLayout, packed]
    have request' : next.capability.request = .value := by rw [same, sameCapability, request]
    have renewal' : renewReceivingDestination id middle.construction = .ok id middle.construction := by
      simp only [renewReceivingDestination, ConstructionM.get, bind, current', pure,
        lookupDestination_result, present', opened']
    simp only [bind] at loop
    rw [loop] at action
    simp only [receivingAction, liftConstruction, renewal', bind] at action
    cases finished : finishDestination id middle.construction with
    | fault reason final => simp only [finished] at action; cases action
    | ok value final =>
      cases value
      simp only [finished, ExecutionStep.ok.injEq, true_and] at action
      subst after
      exact finish_packed_preserves_child_invariants middle.construction final id n next present' opened' packed' request'
        candidates.1 candidates.2 finished

#print axioms bytes_writeLoop_child_invariants
#print axioms build_packed_bytes_child_invariants

end Goose.Proofs.ConstructionAcceptedExecution
