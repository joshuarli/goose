import Goose.Proofs.ConstructionExecutionProtocolWrites

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

local syntax "attach_split_if" : tactic
elab_rules : tactic
  | `(tactic| attach_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no construction condition to split"
      return [yes.mvarId, no.mvarId]

private theorem replace_event_lifecycle (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (events : List ConstructionEvent)
    (present : state.destinations[id]? = some before)
    (capability : after.capability.id = before.capability.id)
    (backing : after.backing = before.backing) (use : after.use = before.use)
    (other : ∀ index, index ≠ id → destinationObservations index events = [])
    (transition : ∀ phase, phase.matchesDestination before → ∃ next,
      runDestinationTrace id phase events = some next ∧ next.matchesDestination after)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with destinations := state.destinations.set! id after, events := state.events ++ events } := by
  refine ⟨destinationTraceProtocol_replace state id before after events present other transition valid.1,
    destinationCapabilities_replace state id after (capability.trans (valid.2.1 id before present)) valid.2.1,
    ?_, destinationOwnersOrdered_replace state id before after present use valid.2.2.2⟩
  apply destinationStorageReferences_replace state id after state.storage (Nat.le_refl _)
  · simpa only [PendingDestination.storage, backing] using (valid.2.2.1 id before present).1
  · simpa only [backing] using (valid.2.2.1 id before present).2
  · exact valid.2.2.1

private theorem built_publish_lifecycle (state : ConstructionState) (id count : Nat)
    (destination : PendingDestination) (present : state.destinations[id]? = some destination)
    (progress : destination.progress = .built count) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with destinations := state.destinations.set! id { destination with progress := .published count }, events := state.events ++ [.publish id] } := by
  apply replace_event_lifecycle state id destination { destination with progress := .published count } [.publish id] present rfl rfl rfl
    (by intro index different; simp [destinationObservations, observeDestination, Ne.symm different]) _ valid
  intro phase matched
  cases phase <;> simp_all [DestinationTracePhase.matchesDestination,
    DestinationTracePhase.matchesProgress, runDestinationTrace, destinationObservations,
    observeDestination, runDestinationObservations, destinationTraceStep]

private theorem built_attach_lifecycle (state : ConstructionState) (id count : Nat)
    (destination : PendingDestination) (present : state.destinations[id]? = some destination)
    (progress : destination.progress = .built count) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with destinations := state.destinations.set! id { destination with progress := .attached count } } := by
  apply destinationLifecycleInvariant_replace_silent state id destination
    { destination with progress := .attached count } state.storage present rfl rfl rfl rfl _ valid
  intro phase matched
  cases phase <;> simp_all [DestinationTracePhase.matchesDestination, DestinationTracePhase.matchesProgress]

private theorem suspended_write_lifecycle (state : ConstructionState) (id count expected finish : Nat)
    (destination : PendingDestination) (present : state.destinations[id]? = some destination)
    (progress : destination.progress = .suspended count expected) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with destinations := state.destinations.set! id { destination with progress := .open (count + 1), writeEnd := finish }, events := state.events ++ [.write id count] } := by
  apply replace_event_lifecycle state id destination
    { destination with progress := .open (count + 1), writeEnd := finish } [.write id count] present rfl rfl rfl
    (by intro index different; simp [destinationObservations, observeDestination, Ne.symm different]) _ valid
  intro phase matched
  cases phase <;> simp_all [DestinationTracePhase.matchesDestination,
    DestinationTracePhase.matchesProgress, runDestinationTrace, destinationObservations,
    observeDestination, runDestinationObservations, destinationTraceStep]

private theorem attach_child_commit (state : ConstructionState) (parentId childId count expected childCount : Nat)
    (parent child : PendingDestination)
    (parentFound : state.destinations[parentId]? = some parent)
    (childFound : state.destinations[childId]? = some child)
    (parentProgress : parent.progress = .suspended count expected)
    (childProgress : child.progress = .built childCount)
    (use : child.use = .child parentId) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with
      destinations := (state.destinations.set! childId { child with progress := .attached childCount }).set! parentId { parent with progress := .open (count + 1), writeEnd := child.writeEnd }
      events := state.events ++ [.write parentId count] } := by
  have ordered : parentId < childId := by simpa only [use] using valid.2.2.2 childId child childFound
  have parentPresent : (state.destinations.set! childId { child with progress := .attached childCount })[parentId]? = some parent := by
    simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Nat.ne_of_lt ordered).symm] using parentFound
  exact suspended_write_lifecycle _ parentId count expected child.writeEnd parent parentPresent parentProgress
    (built_attach_lifecycle state childId childCount child childFound childProgress valid)

theorem attachChild_destination_lifecycle_invariant (parentId childId : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (attachChild parentId childId state).finalState := by
  simp only [attachChild, writableDestination_result, bind]
  cases parentFound : state.destinations[parentId]? with
  | none => exact valid
  | some parent =>
      simp only [parentFound]
      cases parentAllowed : destinationCanWrite state parentId with
      | false => exact valid
      | true =>
          simp only [parentAllowed]
          cases childFound : state.destinations[childId]? with
          | none => exact valid
          | some child =>
              simp only [childFound]
              cases childAllowed : destinationCanWrite state childId with
              | false => exact valid
              | true =>
                  simp only [childAllowed]
                  have parentInside := (Array.getElem?_eq_some_iff.mp parentFound).choose
                  have childInside := (Array.getElem?_eq_some_iff.mp childFound).choose
                  cases parentProgress : parent.progress <;> (try simp only [parentProgress]) <;> try exact valid
                  case suspended count expected =>
                    cases childProgress : child.progress <;> (try simp only [childProgress]) <;> try exact valid
                    case built childCount =>
                      cases use : child.use <;> (try simp only [use]) <;> try exact valid
                      case child owner =>
                        repeat' first
                          | simp only [replaceDestination_result, parentInside, childInside, Array.size_set!,
                              ↓reduceIte, pure, bind, ConstructionM.fail, emit_result, ConstructionResult.finalState]
                          | attach_split_if
                          | exact valid
                        have ownerEqual : owner = parentId := by simp_all
                        subst owner
                        simpa only [parentProgress, childProgress, use] using
                          attach_child_commit state parentId childId count expected childCount parent child
                            parentFound childFound parentProgress childProgress use valid

private theorem attach_extension_commit (state : ConstructionState)
    (parentId childId count expected childCount total finish : Nat)
    (parent child after : PendingDestination)
    (parentFound : state.destinations[parentId]? = some parent)
    (childFound : state.destinations[childId]? = some child)
    (parentProgress : parent.progress = .suspended count expected)
    (childProgress : child.progress = .built childCount)
    (childUse : child.use = .child parentId)
    (capability : after.capability.id = child.capability.id)
    (use : after.use = child.use)
    (writeStorage : after.storage < state.storage.size)
    (receiverStorage : after.backing.receiverStorage < state.storage.size)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with
      destinations := (state.destinations.set! childId { after with progress := .attached childCount }).set! parentId { parent with progress := .built total, writeEnd := finish }
      events := state.events ++ [.publish childId] } := by
  have ordered : parentId < childId := by simpa only [childUse] using valid.2.2.2 childId child childFound
  have attached : DestinationLifecycleInvariant { state with
      destinations := state.destinations.set! childId { after with progress := .attached childCount }
      events := state.events ++ [.publish childId] } := by
    refine ⟨destinationTraceProtocol_replace state childId child _ [.publish childId] childFound
      (by intro index different; simp [destinationObservations, observeDestination, Ne.symm different]) ?_ valid.1,
      destinationCapabilities_replace state childId _ (capability.trans (valid.2.1 childId child childFound)) valid.2.1,
      destinationStorageReferences_replace state childId _ state.storage (Nat.le_refl _) writeStorage receiverStorage valid.2.2.1,
      destinationOwnersOrdered_replace state childId child _ childFound use valid.2.2.2⟩
    intro phase matched
    cases phase <;> simp_all [DestinationTracePhase.matchesDestination,
      DestinationTracePhase.matchesProgress, runDestinationTrace, destinationObservations,
      observeDestination, runDestinationObservations, destinationTraceStep]
  have parentPresent : (state.destinations.set! childId { after with progress := .attached childCount })[parentId]? = some parent := by
    simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Nat.ne_of_lt ordered).symm] using parentFound
  apply destinationLifecycleInvariant_replace_silent
    { state with destinations := state.destinations.set! childId { after with progress := .attached childCount }, events := state.events ++ [.publish childId] } parentId parent
    { parent with progress := .built total, writeEnd := finish } state.storage parentPresent rfl rfl rfl rfl _ attached
  intro phase matched
  cases phase <;> simp_all [DestinationTracePhase.matchesDestination, DestinationTracePhase.matchesProgress]

private theorem built_copy_lifecycle (state : ConstructionState) (id count : Nat)
    (destination : PendingDestination) (source : CopySource)
    (present : state.destinations[id]? = some destination)
    (progress : destination.progress = .built count) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with events := state.events ++ [.copy source id] } := by
  refine ⟨destinationTraceProtocol_emit state id destination [.copy source id] present
    (by intro index different; simp [destinationObservations, observeDestination, Ne.symm different]) ?_ valid.1,
    valid.2⟩
  intro phase matched
  cases phase <;> simp_all [DestinationTracePhase.matchesDestination,
    DestinationTracePhase.matchesProgress, runDestinationTrace, destinationObservations,
    observeDestination, runDestinationObservations, destinationTraceStep]

set_option maxHeartbeats 1600000 in
theorem attachElementExtension_destination_lifecycle_invariant (parentId childId : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (attachElementExtension parentId childId state).finalState := by
  simp only [attachElementExtension, writableDestination_result, bind]
  cases parentFound : state.destinations[parentId]? with
  | none => exact valid
  | some parent =>
      simp only [parentFound]
      cases parentAllowed : destinationCanWrite state parentId with
      | false => exact valid
      | true =>
          simp only [parentAllowed]
          cases childFound : state.destinations[childId]? with
          | none => exact valid
          | some child =>
              simp only [childFound]
              cases childAllowed : destinationCanWrite state childId with
              | false => exact valid
              | true =>
                  simp only [childAllowed]
                  have parentInside := (Array.getElem?_eq_some_iff.mp parentFound).choose
                  have childInside := (Array.getElem?_eq_some_iff.mp childFound).choose
                  have bound := (valid.2.2.1 parentId parent parentFound).1
                  cases parentProgress : parent.progress <;> (try simp only [parentProgress]) <;> try exact valid
                  case suspended count expected =>
                    cases childProgress : child.progress <;> (try simp only [childProgress]) <;> try exact valid
                    case built childCount =>
                      cases use : child.use <;> (try simp only [use]) <;> try exact valid
                      case child owner =>
                        cases backing : child.backing <;> (try simp only [backing]) <;> try exact valid
                        case direct storageId =>
                          by_cases adaptation : child.adaptation.isSome = true
                          · simp only [adaptation, ↓reduceIte, ConstructionM.fail, ConstructionResult.finalState]; exact valid
                          · simp only [adaptation, ↓reduceIte]
                            by_cases ownership : (expected != childId || owner != parentId || storageId != parent.storage || child.capability.request != .value || parent.capability.logicalType.element? != some child.capability.logicalType) = true
                            · simp only [ownership, ↓reduceIte, ConstructionM.fail, ConstructionResult.finalState]; exact valid
                            · simp only [ownership, ↓reduceIte]
                              have ownerEqual : owner = parentId := by
                                apply Classical.byContradiction
                                intro different
                                apply ownership
                                simp only [Bool.or_eq_true, bne_iff_ne]
                                exact Or.inl (Or.inl (Or.inl (Or.inr different)))
                              subst owner
                              have committed : ∀ storage : Array ReceivingStorage, storage.size = state.storage.size →
                                  DestinationLifecycleInvariant { state with
                                    storage := storage
                                    destinations := (state.destinations.set! childId { child with progress := .attached childCount }).set! parentId { parent with progress := .built (count + 1), writeEnd := child.writeEnd }
                                    events := state.events ++ [.publish childId] } := by
                                intro storage size
                                exact attach_extension_commit { state with storage := storage } parentId childId count expected childCount (count + 1) child.writeEnd
                                  parent child child parentFound childFound parentProgress childProgress use rfl rfl
                                  (by simpa only [size] using (valid.2.2.1 childId child childFound).1)
                                  (by simpa only [size] using (valid.2.2.1 childId child childFound).2)
                                  (destinationLifecycleInvariant_storage_frame state storage size valid)
                              simp only [parentProgress, childProgress, use, backing] at committed
                              cases stored : state.storage[parent.storage]?
                              all_goals
                                cases layout : parent.layout
                                all_goals simp only [layout] at committed
                                all_goals repeat' first
                                  | simp only [lookupStorage_result, stored, layout, replaceStorage_result,
                                      replaceDestination_result, parentInside, childInside, Array.size_set!, bound,
                                      ↓reduceIte, pure, bind, ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                  | attach_split_if
                                  | exact valid
                                  | exact committed _ (by simp)

set_option maxHeartbeats 2400000 in
theorem attachExtension_destination_lifecycle_invariant (parentId childId : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (attachExtension parentId childId state).finalState := by
  simp only [attachExtension, writableDestination_result, bind]
  cases parentFound : state.destinations[parentId]? with
  | none => exact valid
  | some parent =>
      simp only [parentFound]
      cases parentAllowed : destinationCanWrite state parentId with
      | false => exact valid
      | true =>
          simp only [parentAllowed]
          cases childFound : state.destinations[childId]? with
          | none => exact valid
          | some child =>
              simp only [childFound]
              cases childAllowed : destinationCanWrite state childId with
              | false => exact valid
              | true =>
                  simp only [childAllowed]
                  have parentInside := (Array.getElem?_eq_some_iff.mp parentFound).choose
                  have childInside := (Array.getElem?_eq_some_iff.mp childFound).choose
                  have bound := (valid.2.2.1 parentId parent parentFound).1
                  cases parentProgress : parent.progress <;> (try simp only [parentProgress]) <;> try exact valid
                  case suspended count expected =>
                    cases childProgress : child.progress <;> (try simp only [childProgress]) <;> try exact valid
                    case built childCount =>
                      cases use : child.use <;> (try simp only [use]) <;> try exact valid
                      case child owner =>
                        by_cases adaptation : child.adaptation.isSome = true
                        · simp only [adaptation, ↓reduceIte, ConstructionM.fail, ConstructionResult.finalState]; exact valid
                        · simp only [adaptation, ↓reduceIte]
                          by_cases ownership : (expected != childId || owner != parentId || child.backing.receiverStorage != parent.storage || child.layout != .elements) = true
                          · simp only [ownership, ↓reduceIte, ConstructionM.fail, ConstructionResult.finalState]; exact valid
                          · simp only [ownership, ↓reduceIte]
                            have ownerEqual : owner = parentId := by
                              apply Classical.byContradiction
                              intro different
                              apply ownership
                              simp only [Bool.or_eq_true, bne_iff_ne]
                              exact Or.inl (Or.inl (Or.inr different))
                            subst owner
                            cases childBacking : child.backing with
                            | direct receiver =>
                                have committed : ∀ storage : Array ReceivingStorage, storage.size = state.storage.size →
                                    DestinationLifecycleInvariant { state with
                                      storage := storage
                                      destinations := (state.destinations.set! childId { child with progress := .attached childCount }).set! parentId { parent with progress := .built (count + childCount), writeEnd := child.writeEnd }
                                      events := state.events ++ [.publish childId] } := by
                                  intro storage size
                                  exact attach_extension_commit { state with storage := storage } parentId childId count expected childCount (count + childCount) child.writeEnd
                                    parent child child parentFound childFound parentProgress childProgress use rfl rfl
                                    (by simpa only [size] using (valid.2.2.1 childId child childFound).1)
                                    (by simpa only [size] using (valid.2.2.1 childId child childFound).2)
                                    (destinationLifecycleInvariant_storage_frame state storage size valid)
                                simp only [parentProgress, childProgress, use, childBacking] at committed
                                cases stored : state.storage[parent.storage]?
                                all_goals
                                  cases layout : parent.layout <;> cases backing : parent.backing
                                  all_goals simp only [layout, backing] at committed
                                  all_goals repeat' first
                                    | simp only [lookupStorage_result, stored, layout, backing, childBacking, use, childProgress, parentProgress,
                                        replaceStorage_result, replaceDestination_result, parentInside, childInside, Array.size_set!, bound,
                                        ↓reduceIte, pure, bind, ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                    | attach_split_if
                                    | exact valid
                                    | exact committed _ (by simp)
                            | staged receiver stageId =>
                                have stageBound : stageId < state.storage.size := by
                                  simpa only [childBacking, PendingDestination.storage, DestinationBacking.writeStorage] using (valid.2.2.1 childId child childFound).1
                                have copied := built_copy_lifecycle state childId childCount child (.storage stageId []) childFound childProgress valid
                                have committed : ∀ (storage : Array ReceivingStorage), storage.size = state.storage.size → ∀ stage : ReceivingStorage,
                                    DestinationLifecycleInvariant { state with
                                      storage := storage
                                      destinations := (state.destinations.set! childId { child with
                                        backing := .direct parent.storage
                                        capability := { child.capability with start := parent.writeEnd }
                                        writeEnd := parent.writeEnd + stage.bytes.size
                                        progress := .attached childCount }).set! parentId { parent with progress := .built (count + childCount), writeEnd := parent.writeEnd + stage.bytes.size }
                                      events := (state.events ++ [.copy (.storage stageId []) childId]) ++ [.publish childId] } := by
                                  intro storage size stage
                                  exact attach_extension_commit { state with storage := storage, events := state.events ++ [.copy (.storage stageId []) childId] }
                                    parentId childId count expected childCount (count + childCount) (parent.writeEnd + stage.bytes.size)
                                    parent child { child with backing := .direct parent.storage, capability := { child.capability with start := parent.writeEnd }, writeEnd := parent.writeEnd + stage.bytes.size }
                                    parentFound childFound parentProgress childProgress use rfl rfl
                                    (by simpa only [PendingDestination.storage, DestinationBacking.writeStorage, size] using bound)
                                    (by simpa only [DestinationBacking.receiverStorage, size] using bound)
                                    (destinationLifecycleInvariant_storage_frame
                                      { state with events := state.events ++ [.copy (.storage stageId []) childId] } storage size copied)
                                simp only [parentProgress, childProgress, use, childBacking] at committed
                                cases stored : state.storage[parent.storage]?
                                all_goals
                                  cases stageFound : state.storage[stageId]?
                                  all_goals
                                    cases layout : parent.layout <;> cases backing : parent.backing
                                    all_goals simp only [layout, backing] at committed
                                    all_goals repeat' first
                                      | simp only [lookupStorage_result, stored, stageFound, layout, backing, childBacking, use, childProgress, parentProgress,
                                          replaceStorage_result, replaceDestination_result, parentInside, childInside, Array.size_set!, Array.size_set!, bound, stageBound,
                                          ↓reduceIte, pure, bind, ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                      | attach_split_if
                                      | exact valid
                                      | exact committed _ (by simp) _

theorem publishElementDestination_destination_lifecycle_invariant (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (publishElementDestination id state).finalState := by
  simp only [publishElementDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact valid
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          cases progress : destination.progress <;> (try simp only [progress]) <;> try exact valid
          case built count =>
            cases use : destination.use <;> (try simp only [use]) <;> try exact valid
            case receiver =>
              cases backing : destination.backing <;> (try simp only [backing]) <;> try exact valid
              case direct storageId =>
                have bound : storageId < state.storage.size := by
                  simpa only [backing, DestinationBacking.receiverStorage] using (valid.2.2.1 id destination present).2
                have committed : ∀ storage : ReceivingStorage,
                    DestinationLifecycleInvariant { state with storage := state.storage.set! storageId storage, destinations := state.destinations.set! id { destination with progress := .published count }, events := state.events ++ [.publish id] } := by
                  intro storage
                  exact built_publish_lifecycle { state with storage := state.storage.set! storageId storage }
                    id count destination present progress
                    (destinationLifecycleInvariant_storage_frame state _ (by simp) valid)
                simp only [backing, use] at committed
                cases stored : state.storage[storageId]?
                all_goals repeat' first
                  | simp only [lookupStorage_result, stored, replaceStorage_result,
                      replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                      ConstructionM.fail, emit_result, ConstructionResult.finalState]
                  | attach_split_if
                  | exact valid
                  | exact committed _


private theorem built_retire_lifecycle (state : ConstructionState) (id count : Nat)
    (destination : PendingDestination) (present : state.destinations[id]? = some destination)
    (progress : destination.progress = .built count) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with destinations := state.destinations.set! id { destination with progress := .retired } } := by
  apply destinationLifecycleInvariant_replace_silent state id destination
    { destination with progress := .retired } state.storage present rfl rfl rfl rfl _ valid
  intro phase matched
  cases phase <;> simp_all [DestinationTracePhase.matchesDestination, DestinationTracePhase.matchesProgress]

theorem retireRepeatedSource_destination_lifecycle_invariant (parentId sourceId : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (retireRepeatedSource parentId sourceId state).finalState := by
  simp only [retireRepeatedSource, writableDestination_result, bind]
  cases parentFound : state.destinations[parentId]? with
  | none => exact valid
  | some parent =>
      simp only [parentFound]
      cases parentAllowed : destinationCanWrite state parentId with
      | false => exact valid
      | true =>
          simp only [parentAllowed]
          cases sourceFound : state.destinations[sourceId]? with
          | none => exact valid
          | some source =>
              simp only [sourceFound]
              cases sourceAllowed : destinationCanWrite state sourceId with
              | false => exact valid
              | true =>
                  simp only [sourceAllowed]
                  have inside := (Array.getElem?_eq_some_iff.mp sourceFound).choose
                  cases parentProgress : parent.progress <;> (try simp only [parentProgress]) <;> try exact valid
                  case «open» parentCount =>
                    cases progress : source.progress <;> (try simp only [progress]) <;> try exact valid
                    case built count =>
                      cases use : source.use <;> (try simp only [use]) <;> try exact valid
                      case receiver =>
                        cases backing : source.backing <;> (try simp only [backing]) <;> try exact valid
                        case direct storageId =>
                          have bound : storageId < state.storage.size := by
                            simpa only [backing, DestinationBacking.receiverStorage] using (valid.2.2.1 sourceId source sourceFound).2
                          have committed : ∀ storage : ReceivingStorage,
                              DestinationLifecycleInvariant { state with storage := state.storage.set! storageId storage, destinations := state.destinations.set! sourceId { source with progress := .retired } } := by
                            intro storage
                            exact built_retire_lifecycle { state with storage := state.storage.set! storageId storage }
                              sourceId count source sourceFound progress
                              (destinationLifecycleInvariant_storage_frame state _ (by simp) valid)
                          simp only [backing, use] at committed
                          cases stored : state.storage[storageId]?
                          all_goals repeat' first
                            | simp only [lookupStorage_result, stored, replaceStorage_result,
                                replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                ConstructionM.get, ConstructionM.fail, emit_result, ConstructionResult.finalState]
                            | attach_split_if
                            | exact valid
                            | exact committed _

end Goose.Proofs.ConstructionExecutionProtocol
