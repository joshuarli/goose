import Goose.Proofs.ConstructionExitReplacementOffset

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionStorage

theorem finish_packed_byte_row (before after : ConstructionState) (id count : Nat)
    (row : PendingDestination) (present : before.destinations[id]? = some row)
    (opened : row.progress = .open count) (packed : row.layout = .packed)
    (request : row.capability.request = .value)
    (executed : finishDestination id before = .ok () after) :
    after.destinations[id]? = some { row with progress := .built count } := by
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
      simpa only [packed, Array.set!_eq_setIfInBounds] using
        (Array.getElem?_setIfInBounds_self_of_lt (xs := before.destinations)
          (a := { row with progress := .built count }) inside)

theorem build_packed_bytes_capability (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id count : Nat) (bytes : List UInt8) (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (valid : OwnershipSourceState before.construction)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    ∃ result, after.construction.destinations[id]? = some result ∧
      result.capability = ready.destination.capability ∧ result.progress = .built (count + bytes.length) := by
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
    obtain ⟨source, lifecycle, current', next, n, present', opened'⟩ :=
      bytes_writeLoop_ownershipSource bytes origin id before middle ready.destination count valid.structural.1.1.1 current ready.present ready.opened loop
    obtain ⟨following, sameLayout, sameCapability, _, _⟩ :=
      bytes_writeLoop_open_backing bytes config.layout origin id count before middle ready current loop
    have same : next = following.destination := Option.some.inj (present'.symm.trans following.present)
    have countEq : n = count + bytes.length := by
      have phases : next.progress = .open (count + bytes.length) := by rw [same]; exact following.opened
      rw [opened'] at phases
      exact DestinationProgress.open.inj phases
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
      refine ⟨{ next with progress := .built n }, finish_packed_byte_row middle.construction final id n next present' opened' packed' request' finished, ?_, ?_⟩
      · simpa only [same] using sameCapability
      · exact congrArg DestinationProgress.built countEq

theorem reserved_byte_built_start_order (fuel : Nat) (config : EvalConfig)
    (reservationBefore reserved : ConstructionState) (incoming selected token count writeCount : Nat)
    (receiverState : ExecutionState) (receiverConstruction : receiverState.construction = reservationBefore)
    (receiver : OpenDestinationBacking config.layout receiverState incoming (.varr (.int .u8)) (count + 1))
    (receiverCurrent : destinationCurrent reservationBefore incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue reservationBefore = .ok (token, selected) reserved)
    (environment : RuntimeActivation) (before after : ExecutionState) (construction : before.construction = reserved)
    (valid : OwnershipSourceState before.construction)
    (ready : OpenDestinationBacking config.layout before selected (.varr (.int .u8)) writeCount)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (selectedCurrent : destinationCurrent before.construction selected = .ok selected)
    (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (built : buildExpr (fuel + 1) config environment selected (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    ∃ result, after.construction.destinations[selected]? = some result ∧
      receiver.destination.capability.start ≤ result.capability.start := by
  obtain ⟨replacement, found, ordered⟩ := reserved_byte_start_order config.layout reservationBefore reserved incoming selected token count
    receiverState receiverConstruction receiver receiverCurrent reservation
  have same : replacement = ready.destination := Option.some.inj (found.symm.trans (by simpa only [construction] using ready.present))
  obtain ⟨result, present, capability, progress⟩ := build_packed_bytes_capability fuel config environment selected writeCount
    bytes origin before after valid ready packed request selectedCurrent built
  exact ⟨result, present, by simpa only [same, capability] using ordered⟩

#print axioms reserved_byte_built_start_order
#print axioms finish_packed_byte_row
#print axioms build_packed_bytes_capability

end Goose.Proofs.ConstructionAcceptedExecution
