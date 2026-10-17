import Goose.Proofs.ConstructionExecutionOwnershipSuccessorAllocation

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

private theorem extensionAllocation_successorMap (parent : DestinationId) (destination : PendingDestination)
    (count : Nat) (storage : ReceivingStorage) (request : ConstructionRequest) (known : Option Nat)
    (backing : DestinationBacking) : FramesSuccessorMap (do
      let start := match backing with | .staged _ _ => 0 | .direct _ => destination.writeEnd
      let state ← ConstructionM.get
      let id := state.destinations.size
      let capability := { destination.capability with id := id, request := request, start := start }
      let child : PendingDestination := ⟨capability, backing, .elements, .child parent, .open 0, start,
        (match backing, destination.layout with | .direct _, .limited _ _ => storage.bytes.size | _, _ => start), known, none⟩
      ConstructionM.set { state with destinations := state.destinations.push child }
      destinationReplace parent { destination with progress := .suspended count id }
      eventEmit (.begin id)
      match backing with | .staged _ _ => eventEmit (.stage id) | .direct _ => pure ()
      pure id) := by
  apply framesSuccessorMap_get_set (fun state => { state with destinations := state.destinations.push (⟨{ destination.capability with id := state.destinations.size, request := request, start := (match backing with | .staged _ _ => 0 | .direct _ => destination.writeEnd) },
    backing, .elements, .child parent, .open 0, (match backing with | .staged _ _ => 0 | .direct _ => destination.writeEnd),
    (match backing, destination.layout with | .direct _, .limited _ _ => storage.bytes.size | _, _ => (match backing with | .staged _ _ => 0 | .direct _ => destination.writeEnd)), known, none⟩) })
  · intro state; rfl
  · intro state; successor_map

set_option maxHeartbeats 800000 in
theorem openExtension_successorMap (parent : DestinationId) (request : ConstructionRequest)
    (known : Option Nat) : FramesSuccessorMap (openExtension parent request known) := by
  unfold openExtension
  apply framesSuccessorMap_bind (writableLookup parent)
  · exact writableLookup_successorMap parent
  · intro destination
    cases progress : destination.progress
    all_goals simp only [progress, constructionM_bind_pure, constructionM_bind_fail]
    all_goals try exact framesSuccessorMap_fail _
    case built count =>
      apply framesSuccessorMap_bind (storageLookup destination.storage)
      · exact framesSuccessorMap_of_frame _ (storageLookup_successorFrame _)
      · intro storage
        cases knownEq : known <;> cases layoutEq : destination.layout <;> cases backingEq : destination.backing
        all_goals simp only [knownEq, layoutEq, backingEq, constructionM_bind_pure, constructionM_bind_fail]
        all_goals first
          | exact framesSuccessorMap_fail _
          | simpa only [knownEq, layoutEq, backingEq, destinationReplace, eventEmit] using
              extensionAllocation_successorMap parent destination count storage request known (.direct destination.storage)
          | (apply framesSuccessorMap_bind (reserveStorage)
             · exact reserveStorage_successorMap _ _
             · intro stage
               simpa only [knownEq, layoutEq, backingEq, destinationReplace, eventEmit, constructionM_bind_pure] using
                 extensionAllocation_successorMap parent destination count storage request known (.staged destination.storage stage))
          | (split
             · exact framesSuccessorMap_fail _
             · simpa only [knownEq, layoutEq, backingEq, destinationReplace, eventEmit] using
                 extensionAllocation_successorMap parent destination count storage request known (.direct destination.storage))

open Lean Elab Term Meta in
elab "extension_overwrite_head" : term => do
  let info ← getConstInfo ``Goose.Construct.openChild
  let some value := info.value? | throwError "missing child definition"
  let some head := value.find? (fun term => match term with
    | .const name _ => name.toString.endsWith ".overwriteBytes"
    | _ => false) | throwError "missing byte overwrite"
  pure head

abbrev extensionOverwrite : ByteArray → Nat → ByteArray → ByteArray := extension_overwrite_head
abbrev extensionPrefixBytes : ByteArray := renewal_prefix_bytes

private theorem elementAllocation_successorMap (parent : DestinationId) (destination : PendingDestination)
    (count : Nat) (storage : ReceivingStorage) (ty : Goose.Construct.Ty)
    (layout : ReceivingLayout) (known : Option Nat) (receiver : Loc) : FramesSuccessorMap (do
      let state ← ConstructionM.get
      let id := state.destinations.size
      let capability := { destination.capability with id := id, receiver := receiver, layout := ty, logicalType := ty, request := .value, start := destination.writeEnd }
      let child : PendingDestination := ⟨capability, .direct destination.storage, layout, .child parent,
        .open 0, destination.writeEnd + (if allocationPrefix layout .value then 4 else 0),
        (match destination.layout with | .limited _ _ => storage.bytes.size | _ => destination.writeEnd), known, none⟩
      ConstructionM.set { state with destinations := state.destinations.push child }
      destinationReplace parent { destination with progress := .suspended count id }
      if allocationPrefix layout .value then
        storageReplace destination.storage { storage with
          bytes := extensionOverwrite storage.bytes destination.writeEnd extensionPrefixBytes }
      eventEmit (.begin id)
      pure id) := by
  apply framesSuccessorMap_get_set (fun state => { state with destinations := state.destinations.push (⟨{ destination.capability with id := state.destinations.size, receiver := receiver, layout := ty, logicalType := ty, request := .value, start := destination.writeEnd },
    .direct destination.storage, layout, .child parent, .open 0,
    destination.writeEnd + (if allocationPrefix layout .value then 4 else 0),
    (match destination.layout with | .limited _ _ => storage.bytes.size | _ => destination.writeEnd), known, none⟩) })
  · intro state; rfl
  · intro state; successor_map

set_option maxHeartbeats 800000 in
theorem openElementExtension_successorMap (parent : DestinationId) (ty : Goose.Construct.Ty)
    (layout : ReceivingLayout) (known : Option Nat) (receiver : Loc) :
    FramesSuccessorMap (openElementExtension parent ty layout known receiver) := by
  unfold openElementExtension
  apply framesSuccessorMap_bind (writableLookup parent)
  · exact writableLookup_successorMap parent
  · intro destination
    cases progress : destination.progress
    all_goals simp only [progress, constructionM_bind_pure, constructionM_bind_fail]
    all_goals try exact framesSuccessorMap_fail _
    case built count =>
      by_cases wrong : (destination.capability.logicalType.element? != some ty) = true
      · simp only [wrong, ↓reduceIte]
        exact framesSuccessorMap_fail _
      · simp only [wrong, ↓reduceIte]
        cases layoutEq : destination.layout <;> cases backingEq : destination.backing
        all_goals simp only [layoutEq, backingEq, Bool.false_eq_true, ↓reduceIte]
        all_goals first
          | exact framesSuccessorMap_fail _
          | (apply framesSuccessorMap_bind (storageLookup destination.storage)
             · exact framesSuccessorMap_of_frame _ (storageLookup_successorFrame _)
             · intro storage
               simpa only [layoutEq, backingEq, destinationReplace, storageReplace, eventEmit,
                 allocationPrefix, extensionOverwrite, extensionPrefixBytes] using
                 elementAllocation_successorMap parent destination count storage ty layout known receiver)
          | (split
             · exact framesSuccessorMap_fail _
             · apply framesSuccessorMap_bind (storageLookup destination.storage)
               · exact framesSuccessorMap_of_frame _ (storageLookup_successorFrame _)
               · intro storage
                 simpa only [layoutEq, backingEq, destinationReplace, storageReplace, eventEmit,
                   allocationPrefix, extensionOverwrite, extensionPrefixBytes] using
                   elementAllocation_successorMap parent destination count storage ty layout known receiver)

end Goose.Proofs.ConstructionExecutionOwnership
