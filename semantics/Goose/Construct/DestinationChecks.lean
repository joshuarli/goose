import Goose.Construct.Destination

namespace Goose.Construct.DestinationChecks
open Goose.Core Goose.Construct

private def capability (request : ConstructionRequest := .value) : Core.Destination Goose.Construct.Ty :=
  ⟨0, ⟨.global 0, []⟩, .grow (.int .u8), .grow (.int .u8), request, 0, 0⟩

private def bytes (values : List Nat) : ByteArray :=
  ⟨(values.map UInt8.ofNat).toArray⟩

private def observe (action : ConstructionM Unit) :
    Option (List Nat × Nat × List ConstructionEvent) :=
  match action ConstructionState.initial with
  | .ok _ state => state.storage[0]?.map fun storage =>
      (storage.bytes.data.toList.map UInt8.toNat, storage.publishedCount, state.events)
  | .fault _ _ => none

private def direct : ConstructionM Unit := do
  let storage ← reserveStorage
  let destination ← openDestination storage capability .packed (some 2)
  writeElement destination (bytes [0])
  writeElement destination (bytes [255])
  finishDestination destination
  publishOperation [destination]

#guard observe direct == some ([2, 0, 0, 0, 0, 255], 2,
  [.begin 0, .write 0 0, .write 0 1, .publish 0])

private def nested : ConstructionM Unit := do
  let storage ← reserveStorage
  let parent ← openDestination storage capability .packed (some 1)
  let child ← openChild parent (.grow (.int .u8)) .packed
  writeElement child (bytes [255])
  finishDestination child
  attachChild parent child
  finishDestination parent
  publishOperation [parent]

#guard observe nested == some ([1, 0, 0, 0, 1, 0, 0, 0, 255], 1,
  [.begin 0, .begin 1, .write 1 0, .write 0 0, .publish 0])

private def unfinishedAppend : ConstructionM Unit := do
  let storage ← reserveStorage (bytes [10]) 1
  let earlier ← openDestination storage (capability .elementRun) .elements (some 1)
  writeElement earlier (bytes [20])
  finishDestination earlier
  publishOperation [earlier]
  let pending ← openDestination storage (capability .elementRun) .elements (some 3)
  writeElement pending (bytes [30])
  writeElement pending (bytes [40])
  abandonTree pending

#guard observe unfinishedAppend == some ([10, 20], 2,
  [.begin 0, .write 0 0, .publish 0, .begin 1, .write 1 0, .write 1 1, .abandon 1])

private def terminalPrefix : ConstructionM Unit := do
  let storage ← reserveStorage
  let destination ← openDestination storage capability .packed (some 2)
  writeElement destination (bytes [1])
  ConstructionM.fail .capacity

#guard match terminalPrefix ConstructionState.initial with
  | .fault .capacity state => state.events == [.begin 0, .write 0 0] &&
      state.storage[0]?.map (·.publishedCount) == some 0
  | _ => false

private def prematurePublish : ConstructionM Unit := do
  let storage ← reserveStorage
  let first ← openDestination storage capability .elements (some 1)
  writeElement first (bytes [10])
  finishDestination first
  let secondStorage ← reserveStorage
  let second ← openDestination secondStorage capability .elements (some 1)
  publishOperation [first, second]

#guard match prematurePublish ConstructionState.initial with
  | .fault .protocol state => state.events == [.begin 0, .write 0 0, .begin 1] &&
      state.storage[0]?.map (·.publishedCount) == some 0
  | _ => false

private def limitedOverflow : ConstructionM Unit := do
  let storage ← reserveStorage (bytes [10]) 1
  let _ ← openDestination storage (capability .elementRun) (.limited 2 1) (some 2)

#guard match limitedOverflow ConstructionState.initial with
  | .fault .capacity state => state.events.isEmpty &&
      state.storage[0]?.map (fun s => s.bytes.data.toList.map UInt8.toNat) == some [10]
  | _ => false

private def staleAbandon : ConstructionM Unit := do
  let storage ← reserveStorage
  let completed ← openDestination storage (capability .elementRun) .elements (some 1)
  writeElement completed (bytes [10])
  finishDestination completed
  publishOperation [completed]
  let independent ← openDestination storage (capability .elementRun) .elements (some 1)
  writeElement independent (bytes [20])
  abandonTree completed

#guard match staleAbandon ConstructionState.initial with
  | .fault .protocol state => state.events ==
      [.begin 0, .write 0 0, .publish 0, .begin 1, .write 1 0] &&
      state.storage[0]?.map (fun s => s.bytes.data.toList.map UInt8.toNat) == some [10, 20]
  | _ => false

private def replacement : ConstructionM Unit := do
  let storage ← reserveStorage (bytes [10]) 1
  let pending ← openDestination storage (capability .elementRun) .elements (some 2)
  writeElement pending (bytes [20])
  let replacement ← openExitReplacement pending
  writeElement replacement (bytes [30])
  finishDestination replacement
  landExitReplacement replacement
  publishOperation [replacement]

#guard observe replacement == some ([10, 30], 2,
  [.begin 0, .write 0 0, .begin 1, .write 1 0, .abandon 0,
   .relocate 1 .exitValue, .publish 1])

private def replacementInChild : ConstructionM Unit := do
  let storage ← reserveStorage
  let parent ← openDestination storage capability .packed (some 1)
  let child ← openChild parent (.varr (.int .u8)) .packed
  writeElement child (bytes [20])
  let replacement ← openExitReplacement child
  writeElement replacement (bytes [30])
  finishDestination replacement
  landExitReplacement replacement
  attachChild parent replacement
  finishDestination parent
  publishOperation [parent]

#guard observe replacementInChild == some ([1, 0, 0, 0, 1, 0, 0, 0, 30], 1,
  [.begin 0, .begin 1, .write 1 0, .begin 2, .write 2 0,
   .abandon 1, .relocate 2 .exitValue, .write 0 0, .publish 0])

private def protectReplacement : ConstructionM Unit := do
  let storage ← reserveStorage
  let pending ← openDestination storage capability .packed (some 2)
  writeElement pending (bytes [20])
  let replacement ← openExitReplacement pending
  writeElement replacement (bytes [30])
  abandonTree pending

#guard match protectReplacement ConstructionState.initial with
  | .fault .protocol state => state.events ==
      [.begin 0, .write 0 0, .begin 1, .write 1 0] &&
      state.storage[0]?.map (fun s => s.bytes.data.toList.map UInt8.toNat) ==
        some [0, 0, 0, 0, 20, 0, 0, 0, 0, 30]
  | _ => false

private def unknownLimited (values : List Nat) : ConstructionM Unit := do
  let storage ← reserveStorage (bytes [10]) 1
  let destination ← openDestination storage (capability .elementRun) (.limited 3 1) none
  for value in values do writeElement destination (bytes [value])
  finishDestination destination
  publishOperation [destination]

#guard observe (unknownLimited [255, 0]) == some ([10, 255, 0], 3,
  [.begin 0, .stage 0, .write 0 0, .write 0 1, .copy (.storage 1 []) 0, .publish 0])
#guard match unknownLimited [255, 0] ConstructionState.initial with
  | .ok _ state => state.storage[1]?.map (·.bytes.size) == some 0
  | _ => false
#guard match unknownLimited [20, 30, 40] ConstructionState.initial with
  | .fault .capacity state => state.events ==
      [.begin 0, .stage 0, .write 0 0, .write 0 1, .write 0 2] &&
      state.storage[0]?.map (fun s => s.bytes.data.toList.map UInt8.toNat) == some [10] &&
      state.storage[0]?.map (·.publishedCount) == some 1
  | _ => false

private def supersededChildWrite : ConstructionM Unit := do
  let storage ← reserveStorage
  let parent ← openDestination storage capability .packed (some 1)
  let child ← openChild parent (.varr (.int .u8)) .packed
  writeElement child (bytes [20])
  let replacement ← openExitReplacement parent
  writeElement replacement (bytes [30])
  writeElement child (bytes [40])

#guard match supersededChildWrite ConstructionState.initial with
  | .fault .protocol state => state.events ==
      [.begin 0, .begin 1, .write 1 0, .begin 2, .write 2 0] &&
      state.storage[0]?.map (fun s => s.bytes.data.toList.map UInt8.toNat) ==
        some [0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 30]
  | _ => false

private def supersededChildCleanup : ConstructionM Unit := do
  let storage ← reserveStorage
  let parent ← openDestination storage capability .packed (some 1)
  let child ← openChild parent (.varr (.int .u8)) .packed
  writeElement child (bytes [20])
  let replacement ← openExitReplacement parent
  writeElement replacement (bytes [30])
  abandonTree child

#guard match supersededChildCleanup ConstructionState.initial with
  | .fault .protocol state => state.events ==
      [.begin 0, .begin 1, .write 1 0, .begin 2, .write 2 0] &&
      state.storage[0]?.map (fun s => s.bytes.data.toList.map UInt8.toNat) ==
        some [0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 30]
  | _ => false

private def protectedCleanup : ConstructionM Unit := do
  let storage ← reserveStorage
  let parent ← openDestination storage capability .packed (some 1)
  let child ← openChild parent (.varr (.int .u8)) .packed
  writeElement child (bytes [20])
  let replacement ← openExitReplacement parent
  writeElement replacement (bytes [30])
  finishDestination replacement
  abandonPreservingExit child replacement
  acknowledgeAbandonment child
  landExitReplacement replacement
  acknowledgeAbandonment parent
  publishOperation [replacement]

#guard observe protectedCleanup == some ([1, 0, 0, 0, 30], 1,
  [.begin 0, .begin 1, .write 1 0, .begin 2, .write 2 0,
   .abandon 1, .abandon 0, .relocate 2 .exitValue, .publish 2])


private def extension : ConstructionM Unit := do
  let storage ← reserveStorage
  let parent ← openDestination storage capability .packed (some 1)
  writeElement parent (bytes [10])
  finishDestination parent
  let child ← openExtension parent .elementRun (some 2)
  recordCopy (.storage 0 []) child
  writeElement child (bytes [20])
  writeElement child (bytes [30])
  finishDestination child
  attachExtension parent child
  truncateConstructionStorage storage 0 6 2 (some parent) false
  removeConstructionHeader parent
  publishOperation [parent]
  appendStdout (bytes [0,255])

#guard observe extension == some ([10,20], 2,
  [.begin 0, .write 0 0, .begin 1, .copy (.storage 0 []) 1,
   .write 1 0, .write 1 1, .publish 1, .relocate 0 .headerRemoval, .publish 0])

#guard match extension ConstructionState.initial with
  | .ok _ state => state.stdout.data.toList.map UInt8.toNat == [0,255]
  | _ => false


private def retainedLimited : ConstructionM Unit := do
  let storage ← reserveStorage (bytes [10,20,30]) 3
  truncateConstructionStorage storage 0 1 1 none true
  let direct ← openDestination storage (capability .elementRun) (.limited 4 1) (some 1)
  writeElement direct (bytes [99])
  finishDestination direct
  publishOperation [direct]
  let staged ← openDestination storage (capability .elementRun) (.limited 4 1) none
  writeElement staged (bytes [7])
  finishDestination staged
  publishOperation [staged]

#guard observe retainedLimited == some ([10,99,7], 3,
  [.begin 0, .write 0 0, .publish 0, .begin 1, .stage 1,
   .write 1 0, .copy (.storage 1 []) 1, .publish 1])

private def retainedNamed : ConstructionM Unit := do
  let storage ← reserveStorage
  let parent ← openDestination storage capability (.limited 4 1) (some 3)
  writeElement parent (bytes [10])
  writeElement parent (bytes [20])
  writeElement parent (bytes [30])
  finishDestination parent
  truncateConstructionStorage storage 0 1 1 (some parent) true
  let child ← openExtension parent .elementRun (some 1)
  writeElement child (bytes [99])
  finishDestination child
  attachExtension parent child
  publishOperation [parent]

#guard observe retainedNamed == some ([10,99,30], 2,
  [.begin 0, .write 0 0, .write 0 1, .write 0 2,
   .begin 1, .write 1 0, .publish 1, .publish 0])


private def namedStageOverflow : ConstructionM Unit := do
  let storage ← reserveStorage
  let parent ← openDestination storage capability (.limited 2 1) (some 1)
  writeElement parent (bytes [10])
  finishDestination parent
  let child ← openExtension parent .elementRun none
  writeElement child (bytes [20])
  writeElement child (bytes [30])
  appendStdout (bytes [255])
  finishDestination child
  attachExtension parent child

#guard match namedStageOverflow ConstructionState.initial with
  | .fault .capacity state =>
      (state.storage[0]?.map (·.bytes.data.toList.map UInt8.toNat)) == some [10] &&
      state.stdout.data.toList.map UInt8.toNat == [255] &&
      state.events == [.begin 0,.write 0 0,.begin 1,.stage 1,.write 1 0,.write 1 1]
  | _ => false


private def namedPackedIntoGrow : ConstructionM Unit := do
  let storage ← reserveStorage
  let destination ← openDestination storage capability .elements (some 2)
  prepareNamedBinding destination (.varr (.int .u8))
  writeElement destination (bytes [0])
  writeElement destination (bytes [255])
  finishDestination destination
  removeConstructionHeader destination
  restoreReceivingLayout destination .elements
  adaptDestinationType destination (.grow (.int .u8))
  publishOperation [destination]

#guard observe namedPackedIntoGrow == some ([0,255], 2,
  [.begin 0,.write 0 0,.write 0 1,.relocate 0 .headerRemoval,.publish 0])


private def namedPackedLimitedOverflow : ConstructionM Unit := do
  let storage ← reserveStorage
  let limitedCapability := { capability with
    layout := .limited (.int .u8) 2
    logicalType := .limited (.int .u8) 2 }
  let destination ← openDestination storage limitedCapability (.limited 2 1) none
  prepareNamedBinding destination (.varr (.int .u8))
  writeElement destination (bytes [10])
  writeElement destination (bytes [20])
  writeElement destination (bytes [30])
  finishDestination destination
  removeConstructionHeader destination
  restoreReceivingLayout destination (.limited 2 1)
  publishOperation [destination]

#guard match namedPackedLimitedOverflow ConstructionState.initial with
  | .fault .capacity state => (state.storage[0]?.map (·.bytes.size)) == some 0 &&
      state.events == [.begin 0,.stage 0,.write 0 0,.write 0 1,.write 0 2,
        .relocate 0 .headerRemoval]
  | _ => false


private def abandonLimitedExtent : ConstructionM Unit := do
  let storage ← reserveStorage (bytes [10,20,30]) 1
  let destination ← openDestination storage (capability .elementRun) (.limited 5 1) (some 3)
  writeElement destination (bytes [99])
  writeElement destination (bytes [88])
  writeElement destination (bytes [77])
  abandonTree destination

#guard observe abandonLimitedExtent == some ([10,99,88], 1,
  [.begin 0,.write 0 0,.write 0 1,.write 0 2,.abandon 0])


private def explicitStageFit : ConstructionM Unit := do
  let storage ← reserveStorage (bytes [10,20,30]) 1
  let destination ← openDestinationDirect storage (capability .elementRun) (.limited 4 1) none
  stageDestination destination
  writeElement destination (bytes [99])
  finishDestination destination
  fitStagedDestination destination

#guard observe explicitStageFit == some ([10,99,30], 1,
  [.begin 0,.stage 0,.write 0 0,.copy (.storage 1 []) 0])

private def explicitKnownStage : ConstructionM Unit := do
  let storage ← reserveStorage
  let destination ← openDestinationDirect storage capability (.limited 4 1) (some 1)
  stageDestination destination

#guard match explicitKnownStage ConstructionState.initial with
  | .fault .protocol state => state.events == [.begin 0] && state.storage.size == 1
  | _ => false


private def replacementStage : ConstructionM Unit := do
  let storage ← reserveStorage
  let root ← openDestinationDirect storage capability (.limited 4 1) none
  let replacement ← openExitReplacement root
  stageDestination replacement

#guard match replacementStage ConstructionState.initial with
  | .fault .protocol state => state.events == [.begin 0,.begin 1] && state.storage.size == 1
  | _ => false


private def prematureNamedFit : ConstructionM Unit := do
  let storage ← reserveStorage
  let destination ← openDestinationDirect storage capability (.limited 2 1) none
  stageDestination destination
  prepareNamedBinding destination (.varr (.int .u8))
  writeElement destination (bytes [99])
  finishDestination destination
  fitStagedDestination destination

#guard match prematureNamedFit ConstructionState.initial with
  | .fault .protocol state => state.events == [.begin 0,.stage 0,.write 0 0] &&
      (state.storage[0]?.map (·.bytes.size)) == some 0
  | _ => false

private def elementExtension : ConstructionM Unit := do
  let storage ← reserveStorage
  let ty := Ty.varr (.int .u8)
  let cap := { capability with layout := .grow ty, logicalType := .grow ty }
  let parent ← openDestination storage cap .elements (some 0)
  finishDestination parent
  let child ← openElementExtension parent ty .packed (some 2) ⟨.global 0, [0]⟩
  writeElement child (bytes [10])
  writeElement child (bytes [20])
  finishDestination child
  attachElementExtension parent child
  publishOperation [parent]
#guard observe elementExtension == some ([2,0,0,0,10,20],1,
  [.begin 0,.begin 1,.write 1 0,.write 1 1,.publish 1,.publish 0])

private def publishedElement : ConstructionM Unit := do
  let storage ← reserveStorage (bytes [7]) 1
  let ty := Ty.varr (.int .u8)
  let cap := { capability with layout := ty, logicalType := ty, receiver := ⟨.global 0,[1]⟩ }
  let destination ← openDestination storage cap .packed (some 2)
  writeElement destination (bytes [10])
  writeElement destination (bytes [20])
  finishDestination destination
  publishElementDestination destination
#guard observe publishedElement == some ([7,2,0,0,0,10,20],2,
  [.begin 0,.write 0 0,.write 0 1,.publish 0])

private def retiredRepeat (reuse : Bool) : ConstructionM Unit := do
  let storage ← reserveStorage
  let parent ← openDestination storage capability .elements (some 1)
  let temporary ← reserveStorage
  let ty := Ty.int .u8
  let source ← openDestination temporary { capability with logicalType := ty,layout := ty }
    (.fixed 1) (some 1)
  writeElement source (bytes [42])
  finishDestination source
  recordCopy (.repeat source) parent
  writeElement parent (bytes [42])
  retireRepeatedSource parent source
  if reuse then recordCopy (.repeat source) parent
#guard observe (retiredRepeat false) == some ([42],0,
  [.begin 0,.begin 1,.write 1 0,.copy (.repeat 1) 0,.write 0 0])
#guard match retiredRepeat true ConstructionState.initial with
  | .fault .protocol state =>
      (state.storage[1]?.map (·.bytes.size)) == some 0 &&
      (state.destinations[1]?.map (·.progress)) == some .retired &&
      (state.destinations[0]?.map (·.progress)) == some (.open 1)
  | _ => false

end Goose.Construct.DestinationChecks
