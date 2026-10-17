import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsForwardFrame
import Goose.Proofs.ConstructionExecutionProtocolAttach

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

local syntax "attach_split_if" : tactic
elab_rules : tactic
  | `(tactic| attach_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no construction condition to split"
      return [yes.mvarId, no.mvarId]

private theorem ownership_attach_child (state : ConstructionState) (parentId childId count expected childCount : Nat)
    (parent child : PendingDestination)
    (parentFound : state.destinations[parentId]? = some parent)
    (childFound : state.destinations[childId]? = some child)
    (parentProgress : parent.progress = .suspended count expected)
    (childProgress : child.progress = .built childCount)
    (use : child.use = .child parentId) (valid : DestinationLifecycleInvariant state) :
    OwnershipForwardRowsFrame state { state with
      destinations := (state.destinations.set! childId { child with progress := .attached childCount }).set! parentId { parent with progress := .open (count + 1), writeEnd := child.writeEnd }
      events := state.events ++ [.write parentId count] } := by
  have ordered : parentId < childId := by simpa only [use] using valid.2.2.2 childId child childFound
  refine ownershipForwardRowsFrame_two_leaf state childId parentId child parent _ _
    childFound parentFound (Nat.ne_of_lt ordered).symm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · simp_all [OwnershipLinkBacking, DestinationBacking.receiverStorage]
  · cases parentUse : parent.use <;> simp [OwnershipLinkBacking, parentUse]
  · simp [ReservationStableProgress, childProgress]
  · simp [ReservationStableProgress, parentProgress]
  · trivial
  · trivial

theorem attachChild_ownership_frame (parentId childId : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    OwnershipForwardRowsFrame state (attachChild parentId childId state).finalState := by
  simp only [attachChild, writableDestination_result, bind]
  cases parentFound : state.destinations[parentId]? with
  | none => exact .refl state
  | some parent =>
      simp only [parentFound]
      cases parentAllowed : destinationCanWrite state parentId with
      | false => exact .refl state
      | true =>
          simp only [parentAllowed]
          cases childFound : state.destinations[childId]? with
          | none => exact .refl state
          | some child =>
              simp only [childFound]
              cases childAllowed : destinationCanWrite state childId with
              | false => exact .refl state
              | true =>
                  simp only [childAllowed]
                  have parentInside := (Array.getElem?_eq_some_iff.mp parentFound).choose
                  have childInside := (Array.getElem?_eq_some_iff.mp childFound).choose
                  cases parentProgress : parent.progress <;> (try simp only [parentProgress]) <;> try exact .refl state
                  case suspended count expected =>
                    cases childProgress : child.progress <;> (try simp only [childProgress]) <;> try exact .refl state
                    case built childCount =>
                      cases use : child.use <;> (try simp only [use]) <;> try exact .refl state
                      case child owner =>
                        repeat' first
                          | simp only [replaceDestination_result, parentInside, childInside, Array.size_set!,
                              ↓reduceIte, pure, bind, ConstructionM.fail, emit_result, ConstructionResult.finalState]
                          | attach_split_if
                          | exact .refl state
                        have ownerEqual : owner = parentId := by simp_all
                        subst owner
                        simpa only [parentProgress, childProgress, use] using
                          ownership_attach_child state parentId childId count expected childCount parent child
                            parentFound childFound parentProgress childProgress use valid


set_option maxHeartbeats 1600000 in
theorem attachElementExtension_ownership_frame (parentId childId : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    OwnershipForwardRowsFrame state (attachElementExtension parentId childId state).finalState := by
  simp only [attachElementExtension, writableDestination_result, bind]
  cases parentFound : state.destinations[parentId]? with
  | none => exact .refl state
  | some parent =>
      simp only [parentFound]
      cases parentAllowed : destinationCanWrite state parentId with
      | false => exact .refl state
      | true =>
          simp only [parentAllowed]
          cases childFound : state.destinations[childId]? with
          | none => exact .refl state
          | some child =>
              simp only [childFound]
              cases childAllowed : destinationCanWrite state childId with
              | false => exact .refl state
              | true =>
                  simp only [childAllowed]
                  have parentInside := (Array.getElem?_eq_some_iff.mp parentFound).choose
                  have childInside := (Array.getElem?_eq_some_iff.mp childFound).choose
                  have bound := (valid.2.2.1 parentId parent parentFound).1
                  cases parentProgress : parent.progress <;> (try simp only [parentProgress]) <;> try exact .refl state
                  case suspended count expected =>
                    cases childProgress : child.progress <;> (try simp only [childProgress]) <;> try exact .refl state
                    case built childCount =>
                      cases use : child.use <;> (try simp only [use]) <;> try exact .refl state
                      case child owner =>
                        cases backing : child.backing <;> (try simp only [backing]) <;> try exact .refl state
                        case direct storageId =>
                          by_cases adaptation : child.adaptation.isSome = true
                          · simp only [adaptation, ↓reduceIte, ConstructionM.fail, ConstructionResult.finalState]; exact .refl state
                          · simp only [adaptation, ↓reduceIte]
                            by_cases ownership : (expected != childId || owner != parentId || storageId != parent.storage || child.capability.request != .value || parent.capability.logicalType.element? != some child.capability.logicalType) = true
                            · simp only [ownership, ↓reduceIte, ConstructionM.fail, ConstructionResult.finalState]; exact .refl state
                            · simp only [ownership, ↓reduceIte]
                              have ownerEqual : owner = parentId := by
                                apply Classical.byContradiction
                                intro different
                                apply ownership
                                simp only [Bool.or_eq_true, bne_iff_ne]
                                exact Or.inl (Or.inl (Or.inl (Or.inr different)))
                              subst owner
                              have committed : ∀ storage : Array ReceivingStorage, storage.size = state.storage.size →
                                  OwnershipForwardRowsFrame state { state with
                                    storage := storage
                                    destinations := (state.destinations.set! childId { child with progress := .attached childCount }).set! parentId { parent with progress := .built (count + 1), writeEnd := child.writeEnd }
                                    events := state.events ++ [.publish childId] } := by
                                intro storage size
                                have ordered : parentId < childId := by simpa only [use] using valid.2.2.2 childId child childFound
                                refine ownershipForwardRowsFrame_two_leaf state childId parentId child parent _ _
                                  childFound parentFound (Nat.ne_of_lt ordered).symm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                                · rfl
                                · rfl
                                · simp_all [OwnershipLinkBacking, DestinationBacking.receiverStorage]
                                · cases parentUse : parent.use <;> simp [OwnershipLinkBacking, parentUse]
                                · simp [ReservationStableProgress, childProgress]
                                · simp [ReservationStableProgress, parentProgress]
                                · trivial
                                · trivial
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
                                  | exact .refl state
                                  | exact committed _ (by simp)


set_option maxHeartbeats 2400000 in
theorem attachExtension_ownership_frame (parentId childId : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    OwnershipForwardRowsFrame state (attachExtension parentId childId state).finalState := by
  simp only [attachExtension, writableDestination_result, bind]
  cases parentFound : state.destinations[parentId]? with
  | none => exact .refl state
  | some parent =>
      simp only [parentFound]
      cases parentAllowed : destinationCanWrite state parentId with
      | false => exact .refl state
      | true =>
          simp only [parentAllowed]
          cases childFound : state.destinations[childId]? with
          | none => exact .refl state
          | some child =>
              simp only [childFound]
              cases childAllowed : destinationCanWrite state childId with
              | false => exact .refl state
              | true =>
                  simp only [childAllowed]
                  have parentInside := (Array.getElem?_eq_some_iff.mp parentFound).choose
                  have childInside := (Array.getElem?_eq_some_iff.mp childFound).choose
                  have bound := (valid.2.2.1 parentId parent parentFound).1
                  cases parentProgress : parent.progress <;> (try simp only [parentProgress]) <;> try exact .refl state
                  case suspended count expected =>
                    cases childProgress : child.progress <;> (try simp only [childProgress]) <;> try exact .refl state
                    case built childCount =>
                      cases use : child.use <;> (try simp only [use]) <;> try exact .refl state
                      case child owner =>
                        by_cases adaptation : child.adaptation.isSome = true
                        · simp only [adaptation, ↓reduceIte, ConstructionM.fail, ConstructionResult.finalState]; exact .refl state
                        · simp only [adaptation, ↓reduceIte]
                          by_cases ownership : (expected != childId || owner != parentId || child.backing.receiverStorage != parent.storage || child.layout != .elements) = true
                          · simp only [ownership, ↓reduceIte, ConstructionM.fail, ConstructionResult.finalState]; exact .refl state
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
                                    OwnershipForwardRowsFrame state { state with
                                      storage := storage
                                      destinations := (state.destinations.set! childId { child with progress := .attached childCount }).set! parentId { parent with progress := .built (count + childCount), writeEnd := child.writeEnd }
                                      events := state.events ++ [.publish childId] } := by
                                  intro storage size
                                  have ordered : parentId < childId := by simpa only [use] using valid.2.2.2 childId child childFound
                                  refine ownershipForwardRowsFrame_two_leaf state childId parentId child parent _ _
                                    childFound parentFound (Nat.ne_of_lt ordered).symm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                                  · rfl
                                  · rfl
                                  · simp_all [OwnershipLinkBacking, DestinationBacking.receiverStorage]
                                  · cases parentUse : parent.use <;> simp [OwnershipLinkBacking, parentUse]
                                  · simp [ReservationStableProgress, childProgress]
                                  · simp [ReservationStableProgress, parentProgress]
                                  · trivial
                                  · trivial
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
                                    | exact .refl state
                                    | exact committed _ (by simp)
                            | staged receiver stageId =>
                                have stageBound : stageId < state.storage.size := by
                                  simpa only [childBacking, PendingDestination.storage, DestinationBacking.writeStorage] using (valid.2.2.1 childId child childFound).1
                                have committed : ∀ (storage : Array ReceivingStorage), storage.size = state.storage.size → ∀ stage : ReceivingStorage,
                                    OwnershipForwardRowsFrame state { state with
                                      storage := storage
                                      destinations := (state.destinations.set! childId { child with
                                        backing := .direct parent.storage
                                        capability := { child.capability with start := parent.writeEnd }
                                        writeEnd := parent.writeEnd + stage.bytes.size
                                        progress := .attached childCount }).set! parentId { parent with progress := .built (count + childCount), writeEnd := parent.writeEnd + stage.bytes.size }
                                      events := (state.events ++ [.copy (.storage stageId []) childId]) ++ [.publish childId] } := by
                                  intro storage size stage
                                  have ordered : parentId < childId := by simpa only [use] using valid.2.2.2 childId child childFound
                                  refine ownershipForwardRowsFrame_two_leaf state childId parentId child parent _ _
                                    childFound parentFound (Nat.ne_of_lt ordered).symm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                                  · rfl
                                  · rfl
                                  · simp_all [OwnershipLinkBacking, DestinationBacking.receiverStorage]
                                  · cases parentUse : parent.use <;> simp [OwnershipLinkBacking, parentUse]
                                  · simp [ReservationStableProgress, childProgress]
                                  · simp [ReservationStableProgress, parentProgress]
                                  · trivial
                                  · trivial
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
                                      | exact .refl state
                                      | exact committed _ (by simp) _


theorem publishElementDestination_ownership_frame (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    OwnershipForwardRowsFrame state (publishElementDestination id state).finalState := by
  simp only [publishElementDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          cases progress : destination.progress <;> (try simp only [progress]) <;> try exact .refl state
          case built count =>
            cases use : destination.use <;> (try simp only [use]) <;> try exact .refl state
            case receiver =>
              cases backing : destination.backing <;> (try simp only [backing]) <;> try exact .refl state
              case direct storageId =>
                have bound : storageId < state.storage.size := by
                  simpa only [backing, DestinationBacking.receiverStorage] using (valid.2.2.1 id destination present).2
                have committed : ∀ storage : ReceivingStorage,
                    OwnershipForwardRowsFrame state { state with storage := state.storage.set! storageId storage, destinations := state.destinations.set! id { destination with progress := .published count }, events := state.events ++ [.publish id] } := by
                  intro storage
                  refine ownershipForwardRowsFrame_replace_leaf state id destination _ present ?_ ?_ ?_ ?_
                  · rfl
                  · simp [OwnershipLinkBacking, use]
                  · simp [progress, ReservationStableProgress]
                  · trivial
                simp only [backing, use] at committed
                cases stored : state.storage[storageId]?
                all_goals repeat' first
                  | simp only [lookupStorage_result, stored, replaceStorage_result,
                      replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                      ConstructionM.fail, emit_result, ConstructionResult.finalState]
                  | attach_split_if
                  | exact .refl state
                  | exact committed _



theorem retireRepeatedSource_ownership_frame (parentId sourceId : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    OwnershipForwardRowsFrame state (retireRepeatedSource parentId sourceId state).finalState := by
  simp only [retireRepeatedSource, writableDestination_result, bind]
  cases parentFound : state.destinations[parentId]? with
  | none => exact .refl state
  | some parent =>
      simp only [parentFound]
      cases parentAllowed : destinationCanWrite state parentId with
      | false => exact .refl state
      | true =>
          simp only [parentAllowed]
          cases sourceFound : state.destinations[sourceId]? with
          | none => exact .refl state
          | some source =>
              simp only [sourceFound]
              cases sourceAllowed : destinationCanWrite state sourceId with
              | false => exact .refl state
              | true =>
                  simp only [sourceAllowed]
                  have inside := (Array.getElem?_eq_some_iff.mp sourceFound).choose
                  cases parentProgress : parent.progress <;> (try simp only [parentProgress]) <;> try exact .refl state
                  case «open» parentCount =>
                    cases progress : source.progress <;> (try simp only [progress]) <;> try exact .refl state
                    case built count =>
                      cases use : source.use <;> (try simp only [use]) <;> try exact .refl state
                      case receiver =>
                        cases backing : source.backing <;> (try simp only [backing]) <;> try exact .refl state
                        case direct storageId =>
                          have bound : storageId < state.storage.size := by
                            simpa only [backing, DestinationBacking.receiverStorage] using (valid.2.2.1 sourceId source sourceFound).2
                          have committed : ∀ storage : ReceivingStorage,
                              OwnershipForwardRowsFrame state { state with storage := state.storage.set! storageId storage, destinations := state.destinations.set! sourceId { source with progress := .retired } } := by
                            intro storage
                            refine ownershipForwardRowsFrame_replace_leaf state sourceId source _ sourceFound ?_ ?_ ?_ ?_
                            · rfl
                            · simp [OwnershipLinkBacking, use]
                            · simp [progress, ReservationStableProgress]
                            · trivial
                          simp only [backing, use] at committed
                          cases stored : state.storage[storageId]?
                          all_goals repeat' first
                            | simp only [lookupStorage_result, stored, replaceStorage_result,
                                replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                ConstructionM.get, ConstructionM.fail, emit_result, ConstructionResult.finalState]
                            | attach_split_if
                            | exact .refl state
                            | exact committed _

end Goose.Proofs.ConstructionExecutionOwnership
