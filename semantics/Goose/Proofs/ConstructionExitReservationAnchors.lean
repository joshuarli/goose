import Goose.Proofs.ConstructionExitReservationAncestry
import Goose.Proofs.ConstructionExecutionOwnershipInactivePrimitives

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem open_replacement_selected_active (before after : ConstructionState) (incoming selected count : Nat)
    (row : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some row) (opened : row.progress = .open count)
    (stored : before.storage[row.storage]? = some storage)
    (executed : openExitReplacement incoming before = .ok selected after) :
    ∃ replacement, after.destinations[selected]? = some replacement ∧ activeProgress replacement.progress = true := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [openExitReplacement, writableDestination_result, present, bind] at executed
  cases allowed : destinationCanWrite before incoming with
  | false => simp [allowed] at executed
  | true =>
    simp only [allowed, opened, pure, bind, lookupStorage_result, stored, ConstructionM.get,
      ConstructionM.set, replaceDestination_result, replaceStorage_result, emit_result,
      Array.size_push, Nat.lt_succ_of_lt inside, storageInside, Array.size_setIfInBounds, ↓reduceIte] at executed
    split at executed <;>
      simp only [Nat.lt_succ_of_lt inside, storageInside, ↓reduceIte, bind, pure] at executed <;>
      cases executed <;>
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne,
        Nat.ne_of_lt inside, Array.getElem?_push, activeProgress]

theorem accepted_open_reservation_anchors (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (channels : List Channel) (carriers : List Goose.Construct.Carrier)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (covered : ∀ id, .completed id ∈ ambient.retained → ∃ frame ∈ pending, .completed id ∈ frame.carriers) :
    RetainedReplacementAnchors reserved (OwnershipAmbient.retained (.exitChannels [token] channels carriers :: ambient)) := by
  obtain ⟨allocated, replacement, appended, source, _, _⟩ :=
    accepted_open_reservation_allocation config initialized before reserved incoming selected token count receiver.destination
      receiver.present receiver.opened current ambient types live regions pending [] [] world reservation
  have fresh := reserve_open_replacement_fresh before.construction reserved incoming selected token count receiver.destination receiver.storage
    receiver.present receiver.opened receiver.bytes current reservation
  have parent := (reserve_open_receiver_snapshot before.construction reserved incoming selected token count receiver.destination
    receiver.present receiver.opened current reservation).1
  have rows := reserve_open_other_rows before.construction reserved incoming selected token count receiver.destination receiver.storage
    receiver.present receiver.opened receiver.bytes current reservation
  obtain ⟨selectedRow, selectedFound, selectedActive⟩ := open_replacement_selected_active before.construction allocated incoming selected (count + 1)
    receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes replacement
  have selectedAfter : reserved.destinations[selected]? = some selectedRow := by simpa only [appended] using selectedFound
  have support := constructionPrimitive_replacementSupportExtension (openExitReplacement incoming) (.openExitReplacement incoming)
    before.construction world.ownership.source.structural.1.1.1
  rw [replacement] at support
  have extension := openExitReplacement_ownership_source incoming before.construction world.ownership.source.structural.1.1.1
  rw [replacement] at extension
  have extensionAfter : OwnershipSourceExtension before.construction reserved := by
    simpa only [ConstructionResult.finalState, appended, OwnershipSourceExtension] using extension
  have allBound := completed_carriers_bounded_by_pending config initialized before ambient types live regions pending world covered
  intro id row found inactive supported
  have notSelected : id ≠ selected := by
    intro same
    subst id
    have equal := Option.some.inj (found.symm.trans selectedAfter)
    subst row
    rw [selectedActive] at inactive
    cases inactive
  have notIncoming : id ≠ incoming := by
    intro same
    subst id
    have equal := Option.some.inj (found.symm.trans parent)
    subst row
    simp [activeProgress] at inactive
  have oldBound : id < before.construction.destinations.size := by
    have bound : id < before.construction.destinations.size + 1 := by
      simpa only [rows.1] using (Array.getElem?_eq_some_iff.mp found).1
    have different : id ≠ before.construction.destinations.size := by simpa only [fresh] using notSelected
    exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ bound) different
  have oldFound : before.construction.destinations[id]? = some row := by
    rw [← rows.2 id notIncoming oldBound]
    exact found
  have allocatedSupport : ReplacementSupported allocated id :=
    replacementSupported_congr_destinations reserved allocated (by simp only [appended]) id supported
  have oldSupport : ReplacementSupported before.construction id := support id oldBound allocatedSupport
  obtain ⟨kept, member, descendant⟩ := world.ownership.retention.anchors id row oldFound inactive oldSupport
  have descendantAfter := destinationDescendant_source_old before.construction reserved
    world.ownership.source.structural.1.1.1.2.2.2 extensionAfter (by rw [rows.1]; omega)
    id kept (allBound kept member)
  refine ⟨kept, ?_, ?_⟩
  · simp only [OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers, completedCarrierIds,
      List.filterMap_append, List.mem_append]
    exact Or.inr member
  · rw [descendantAfter]
    exact descendant

#print axioms open_replacement_selected_active
#print axioms accepted_open_reservation_anchors

theorem accepted_open_reservation_execution_context (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (channels : List Channel) (carriers : List Goose.Construct.Carrier)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (history : ReservationReferencesBounded before.construction ambient)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (covered : ∀ id, .completed id ∈ ambient.retained → ∃ frame ∈ pending, .completed id ∈ frame.carriers) :
    OwnershipExecutionContext { before with construction := reserved } (.exitChannels [token] channels carriers :: ambient) := by
  have source := accepted_open_reservation_source config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending world reservation
  have parts := accepted_open_reservation_context_parts config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending channels carriers world history reservation
  have anchors := accepted_open_reservation_anchors config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending channels carriers world reservation covered
  have boundaries := accepted_open_reservation_boundaries config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending channels carriers world history reservation covered
  exact ⟨source, ⟨source.structural.1, anchors, boundaries⟩,
    parts.2.2.2.1, parts.2.2.1, parts.2.2.2.2.2.2, parts.2.2.2.2.2.1, parts.2.2.2.2.1⟩

#print axioms accepted_open_reservation_execution_context

end Goose.Proofs.ConstructionAcceptedExecution
