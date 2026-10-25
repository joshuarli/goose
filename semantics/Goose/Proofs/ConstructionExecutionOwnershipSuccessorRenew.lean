import Goose.Proofs.ConstructionExecutionOwnershipSuccessorFrames

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

open Lean Elab Term Meta in
elab "renewal_prefix_test" : term => do
  let info ← getConstInfo ``Goose.Construct.renewReceivingDestination
  let some value := info.value? | throwError "missing renewal definition"
  let some head := value.find? (fun term => match term with
    | .const name _ => name.toString.endsWith ".hasPrefix"
    | _ => false) | throwError "missing prefix test"
  pure head

open Lean Elab Term Meta in
elab "renewal_prefix_bytes" : term => do
  let info ← getConstInfo ``Goose.Construct.renewReceivingDestination
  let some value := info.value? | throwError "missing renewal definition"
  let some head := value.find? (fun term => match term with
    | .const name _ => name.toString.endsWith ".lengthPrefix"
    | _ => false) | throwError "missing prefix bytes"
  pure head

private abbrev renewalPrefix : ReceivingLayout → ConstructionRequest → Bool := renewal_prefix_test
private abbrev renewalPrefixBytes : ByteArray := renewal_prefix_bytes

private theorem renewalEnding_successorFrame (backing : DestinationBacking) (next : DestinationId) :
    FramesSuccessors (do
      eventEmit (.begin next)
      match backing with
      | .staged _ _ => eventEmit (.stage next)
      | .direct _ => pure ()
      pure next) := by
  apply framesSuccessors_bind
  · exact eventEmit_successorFrame _
  · intro begun
    cases backing with
    | direct _ => exact framesSuccessors_pure _
    | staged _ _ =>
        apply framesSuccessors_bind
        · exact eventEmit_successorFrame _
        · intro staged
          exact framesSuccessors_pure _

private theorem renewalWrites_successorFrame (snapshot : PendingDestination) (storage : ReceivingStorage)
    (needsPrefix : Bool) (prefixBytes : ByteArray) (next : DestinationId) :
    FramesSuccessors (do
      storageReplace snapshot.storage storage
      if needsPrefix then storageReplace snapshot.storage { storage with bytes := storage.bytes ++ prefixBytes }
      eventEmit (.begin next)
      match snapshot.backing with
      | .staged _ _ => eventEmit (.stage next)
      | .direct _ => pure ()
      pure next) := by
  apply framesSuccessors_bind
  · exact storageReplace_successorFrame _ _
  · intro stored
    cases needsPrefix with
    | false => exact renewalEnding_successorFrame _ _
    | true =>
        apply framesSuccessors_bind
        · exact storageReplace_successorFrame _ _
        · intro prefixed
          exact renewalEnding_successorFrame _ _

private theorem renewalSuffix_successors (state : ConstructionState) (id : DestinationId)
    (snapshot row : PendingDestination) (storage : ReceivingStorage)
    (update : Option (DestinationId × PendingDestination)) (needsPrefix : Bool) (prefixBytes : ByteArray)
    (inside : id < state.destinations.size) (valid : DestinationSuccessorsValid state) :
    DestinationSuccessorsValid ((do
      if let some (parent, owner) := update then destinationReplace parent owner
      storageReplace snapshot.storage storage
      if needsPrefix then storageReplace snapshot.storage { storage with bytes := storage.bytes ++ prefixBytes }
      eventEmit (.begin state.destinations.size)
      match snapshot.backing with
      | .staged _ _ => eventEmit (.stage state.destinations.size)
      | .direct _ => pure ()
      pure state.destinations.size) { state with
        destinations := state.destinations.push row
        destinationSuccessors := (id, state.destinations.size) :: state.destinationSuccessors }).finalState := by
  let allocated := { state with destinations := state.destinations.push row }
  have retained : DestinationSuccessorsValid allocated :=
    destinationSuccessorsValid_extension state allocated valid rfl (by simp [allocated])
  have after : DestinationSuccessorsValid { state with
      destinations := state.destinations.push row
      destinationSuccessors := (id, state.destinations.size) :: state.destinationSuccessors } := by
    simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, allocated]
      using destinationSuccessorsValid_prepend allocated state.destinations.size [id] retained
        (by simp [allocated]) (by intro next member; simp only [List.mem_singleton] at member; simpa only [member] using inside)
  apply framesSuccessors_preserves _ ?_ _ after
  cases update with
  | none => exact renewalWrites_successorFrame _ _ _ _ _
  | some update =>
      rcases update with ⟨parent, owner⟩
      apply framesSuccessors_bind
      · exact destinationReplace_successorFrame _ _
      · intro restored
        exact renewalWrites_successorFrame _ _ _ _ _

private theorem renewalAllocation_successors (state : ConstructionState) (id : DestinationId)
    (snapshot row : PendingDestination) (storage : ReceivingStorage) (needsPrefix : Bool) (prefixBytes : ByteArray)
    (inside : id < state.destinations.size) (valid : DestinationSuccessorsValid state) :
    DestinationSuccessorsValid ((do
      let ownerUpdate ← match snapshot.use with
        | .receiver => pure none
        | .child parent => do
            let owner ← destinationLookup parent
            match owner.progress with
            | .suspended count expected =>
                if expected != id then ConstructionM.fail .ownership
                pure (some (parent, { owner with progress := .suspended count state.destinations.size }))
            | _ => ConstructionM.fail .protocol
        | .replacement parent => do
            let owner ← destinationLookup parent
            match owner.progress with
            | .exiting count expected =>
                if expected != id then ConstructionM.fail .ownership
                pure (some (parent, { owner with progress := .exiting count state.destinations.size }))
            | _ => ConstructionM.fail .protocol
      ConstructionM.set { state with
        destinations := state.destinations.push row
        destinationSuccessors := (id, state.destinations.size) :: state.destinationSuccessors }
      if let some (parent, owner) := ownerUpdate then destinationReplace parent owner
      storageReplace snapshot.storage storage
      if needsPrefix then storageReplace snapshot.storage { storage with bytes := storage.bytes ++ prefixBytes }
      eventEmit (.begin state.destinations.size)
      match snapshot.backing with
      | .staged _ _ => eventEmit (.stage state.destinations.size)
      | .direct _ => pure ()
      pure state.destinations.size) state).finalState := by
  cases use : snapshot.use with
  | receiver =>
      simpa only [use, bind, pure, ConstructionM.set] using
        renewalSuffix_successors state id snapshot row storage none needsPrefix prefixBytes inside valid
  | child parentId =>
      simp only [use, destinationLookup, lookupDestination_result, bind]
      cases present : state.destinations[parentId]? with
      | none => exact valid
      | some owner =>
          simp only [present]
          cases progress : owner.progress
          all_goals simp only [progress, ConstructionM.fail, bind, pure]
          all_goals try exact valid
          rename_i count expected
          split
          · exact valid
          · simpa only [bind, pure, ConstructionM.set] using
              renewalSuffix_successors state id snapshot row storage
                (some (parentId, { owner with progress := .suspended count state.destinations.size }))
                needsPrefix prefixBytes inside valid
  | replacement parentId =>
      simp only [use, destinationLookup, lookupDestination_result, bind]
      cases present : state.destinations[parentId]? with
      | none => exact valid
      | some owner =>
          simp only [present]
          cases progress : owner.progress
          all_goals simp only [progress, ConstructionM.fail, bind, pure]
          all_goals try exact valid
          rename_i count expected
          split
          · exact valid
          · simpa only [bind, pure, ConstructionM.set] using
              renewalSuffix_successors state id snapshot row storage
                (some (parentId, { owner with progress := .exiting count state.destinations.size }))
                needsPrefix prefixBytes inside valid

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem renewReceivingDestination_successors (incoming : DestinationId) (state : ConstructionState)
    (valid : DestinationSuccessorsValid state) :
    DestinationSuccessorsValid (renewReceivingDestination incoming state).finalState := by
  simp only [renewReceivingDestination, ConstructionM.get, bind]
  cases resolved : destinationCurrent state incoming with
  | error reason => simpa only [resolved, ConstructionM.fail, ConstructionResult.finalState, ConstructionResult.finalState] using valid
  | ok id =>
      simp only [resolved, pure, bind, lookupDestination_result]
      cases present : state.destinations[id]? with
      | none => simpa only [present, ConstructionResult.finalState] using valid
      | some destination =>
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          simp only [present]
          cases progress : destination.progress
          all_goals simp only [progress, pure, bind, ConstructionM.get]
          all_goals try exact valid
          all_goals
            cases saved : state.destinationResumptions.lookup id with
            | none => simpa only [saved, ConstructionM.fail, ConstructionResult.finalState, ConstructionResult.finalState] using valid
            | some snapshot =>
                simp only [saved, lookupStorage_result, bind]
                cases stored : state.storage[snapshot.storage]? with
                | none => simpa only [stored, ConstructionResult.finalState] using valid
                | some storage =>
                    simp only [stored]
                    cases adaptation : snapshot.adaptation with
                    | none =>
                        simp only [adaptation, pure, bind]
                        by_cases fits : storage.bytes.size < snapshot.capability.start
                        · simp only [fits, ↓reduceIte, ConstructionM.fail, bind, pure, ConstructionResult.finalState]
                          exact valid
                        · simp only [fits, ↓reduceIte, pure, bind]
                          have preserved := renewalAllocation_successors state id snapshot ({ snapshot with capability := { snapshot.capability with id := state.destinations.size }, progress := .open 0, writeEnd := snapshot.capability.start + (if renewalPrefix snapshot.layout snapshot.capability.request then 4 else 0) }) storage (renewalPrefix snapshot.layout snapshot.capability.request) renewalPrefixBytes inside valid
                          simp (config := { maxSteps := 100000 }) only [adaptation, renewalPrefix,
                            renewalPrefixBytes, bind, pure, ConstructionM.fail, destinationLookup,
                            storageReplace, destinationReplace, eventEmit, lookupDestination_result,
                            ConstructionM.set, replaceStorage_result, replaceDestination_result,
                            emit_result, ConstructionResult.finalState] at preserved ⊢
                          repeat' first
                            | exact preserved
                            | (split at preserved <;> simp_all (config := { maxSteps := 100000 }) only [bind, pure,
                                ConstructionResult.finalState, Array.size_set!, Array.size_push, ↓reduceIte])
                    | some receiving =>
                        simp only [adaptation]
                        by_cases needs : (renewalPrefix receiving.layout receiving.request &&
                            !renewalPrefix snapshot.layout snapshot.capability.request) = true
                        · dsimp only [renewalPrefix] at needs
                          simp only [needs, ↓reduceIte]
                          by_cases geometry : (snapshot.capability.start != receiving.start + 4 ||
                              storage.bytes.size != receiving.start) = true
                          · simp only [geometry, ↓reduceIte, ConstructionM.fail, bind, pure,
                              ConstructionResult.finalState]
                            exact valid
                          · simp only [geometry, ↓reduceIte, pure, bind]
                            let updated : ReceivingStorage := { storage with bytes := storage.bytes ++ renewalPrefixBytes }
                            by_cases fits : updated.bytes.size < snapshot.capability.start
                            · dsimp only [updated, renewalPrefixBytes] at fits
                              simp only [fits, ↓reduceIte, ConstructionM.fail, bind, pure, ConstructionResult.finalState]
                              exact valid
                            · dsimp only [updated, renewalPrefixBytes] at fits
                              simp only [fits, ↓reduceIte, pure, bind]
                              have preserved := renewalAllocation_successors state id snapshot ({ snapshot with capability := { snapshot.capability with id := state.destinations.size }, progress := .open 0, writeEnd := snapshot.capability.start + (if renewalPrefix snapshot.layout snapshot.capability.request then 4 else 0) }) updated (renewalPrefix snapshot.layout snapshot.capability.request) renewalPrefixBytes inside valid
                              dsimp only [updated] at preserved
                              simp (config := { maxSteps := 100000 }) only [adaptation, renewalPrefix,
                                renewalPrefixBytes, bind, pure, ConstructionM.fail, destinationLookup,
                                storageReplace, destinationReplace, eventEmit, lookupDestination_result,
                                ConstructionM.set, replaceStorage_result, replaceDestination_result,
                                emit_result, ConstructionResult.finalState] at preserved ⊢
                              repeat' first
                                | exact preserved
                                | (split at preserved <;> simp_all (config := { maxSteps := 100000 }) only [bind, pure,
                                    ConstructionResult.finalState, Array.size_set!, Array.size_push, ↓reduceIte])
                        · dsimp only [renewalPrefix] at needs
                          simp only [needs, ↓reduceIte, pure, bind]
                          by_cases fits : storage.bytes.size < snapshot.capability.start
                          · simp only [fits, ↓reduceIte, ConstructionM.fail, bind, pure, ConstructionResult.finalState]
                            exact valid
                          · simp only [fits, ↓reduceIte, pure, bind]
                            have preserved := renewalAllocation_successors state id snapshot ({ snapshot with capability := { snapshot.capability with id := state.destinations.size }, progress := .open 0, writeEnd := snapshot.capability.start + (if renewalPrefix snapshot.layout snapshot.capability.request then 4 else 0) }) storage (renewalPrefix snapshot.layout snapshot.capability.request) renewalPrefixBytes inside valid
                            simp (config := { maxSteps := 100000 }) only [adaptation, renewalPrefix,
                              renewalPrefixBytes, bind, pure, ConstructionM.fail, destinationLookup,
                              storageReplace, destinationReplace, eventEmit, lookupDestination_result,
                              ConstructionM.set, replaceStorage_result, replaceDestination_result,
                              emit_result, ConstructionResult.finalState] at preserved ⊢
                            repeat' first
                              | exact preserved
                              | (split at preserved <;> simp_all (config := { maxSteps := 100000 }) only [bind, pure,
                                  ConstructionResult.finalState, Array.size_set!, Array.size_push, ↓reduceIte])

end Goose.Proofs.ConstructionExecutionOwnership
