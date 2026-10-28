import Goose.Proofs.ConstructionExitByteParent

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionStorage

theorem finish_packed_byte_other_row (before after : ConstructionState) (id other count : Nat)
    (row : PendingDestination) (present : before.destinations[id]? = some row)
    (opened : row.progress = .open count) (packed : row.layout = .packed)
    (request : row.capability.request = .value) (different : other ≠ id)
    (executed : finishDestination id before = .ok () after) :
    after.destinations[other]? = before.destinations[other]? := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  simp only [finishDestination, writableDestination_result, present, bind] at executed
  cases allowed : destinationCanWrite before id with
  | false => simp only [allowed] at executed; cases executed
  | true =>
    simp only [allowed, opened, packed, hasPrefix_result, request, beq_self_eq_true,
      Bool.and_self, ↓reduceIte, lookupStorage_result, bind] at executed
    cases stored : before.storage[row.storage]? with
    | none => simp only [stored] at executed; cases executed
    | some storage =>
      have bound := (Array.getElem?_eq_some_iff.mp stored).1
      simp only [stored, replaceStorage_result, replaceDestination_result, bound, inside,
        bind, pure, ↓reduceIte] at executed
      cases executed
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Ne.symm different]

theorem build_packed_bytes_other_row (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id count other : Nat) (bytes : List UInt8) (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (valid : OwnershipSourceState before.construction)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id) (different : other ≠ id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    after.construction.destinations[other]? = before.construction.destinations[other]? := by
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
    have parent := bytes_writeLoop_other_row bytes origin id before middle ready.destination count other different
      valid current ready.present ready.opened loop
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
      exact (finish_packed_byte_other_row middle.construction final id other n next present' opened' packed' request' different finished).trans parent

theorem reserved_parent_survives_byte_build (fuel : Nat) (config : EvalConfig)
    (reservationBefore reserved : ConstructionState) (incoming selected token count writeCount : Nat)
    (original : PendingDestination) (present : reservationBefore.destinations[incoming]? = some original)
    (opened : original.progress = .open (count + 1))
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
    (releaseScopeState environment scope scopeInst after).construction.destinations[incoming]? =
      some { original with progress := .exiting (count + 1) selected } := by
  have parent := (reserve_open_receiver_snapshot reservationBefore reserved incoming selected token count original
    present opened receiverCurrent reservation).1
  have distinct : incoming ≠ selected := by
    intro equal
    have same : { original with progress := .exiting (count + 1) selected } = ready.destination := by
      apply Option.some.inj
      rw [← construction, equal] at parent
      exact parent.symm.trans ready.present
    have impossible := congrArg PendingDestination.progress same
    simp only [ready.opened] at impossible
    cases impossible
  have unchanged := build_packed_bytes_other_row fuel config environment selected writeCount incoming bytes origin
    before after valid ready packed request selectedCurrent distinct built
  simpa only [releaseScopeState, unchanged, construction] using parent

#print axioms reserved_parent_survives_byte_build
#print axioms finish_packed_byte_other_row
#print axioms build_packed_bytes_other_row

end Goose.Proofs.ConstructionAcceptedExecution
