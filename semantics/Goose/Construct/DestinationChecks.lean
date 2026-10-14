import Goose.Construct.Destination

namespace Goose.Construct.DestinationChecks
open Goose.Core Goose.Construct

private def capability (request : ConstructionRequest := .value) : Destination :=
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
  let _ ← openDestination storage (capability .elementRun) (.limited 2) (some 2)

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

end Goose.Construct.DestinationChecks
