import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsMutations

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

local syntax "ownership_header_split_if" : tactic
elab_rules : tactic
  | `(tactic| ownership_header_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no ownership header condition to split"
      return [yes.mvarId, no.mvarId]

theorem removeConstructionHeader_ownership_rows (id : DestinationId)
    (state : ConstructionState) :
    OwnershipLinkRowsFrame state (removeConstructionHeader id state).finalState := by
  simp only [removeConstructionHeader, writableDestination_result, bind]
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
            have removed : ∀ storage : ReceivingStorage,
                OwnershipLinkRowsFrame state { state with
                  storage := state.storage.set! destination.storage storage
                  destinations := state.destinations.set! id { destination with layout := .elements, writeEnd := destination.writeEnd - 4 },
                  events := state.events ++ [.relocate id .headerRemoval] } := by
              intro storage
              refine ownershipLinkRowsFrame_replace_mutable state id destination _ present ?_ ?_ ?_
              · rfl
              · cases use : destination.use <;> simp [OwnershipLinkBacking, use]
              · simp [progress, ReservationStableProgress]
            simp only [progress] at removed
            cases stored : state.storage[destination.storage]? with
            | none =>
                repeat' first
                  | simp only [lookupStorage_result, stored, bind, ConstructionM.fail,
                      ConstructionResult.finalState]
                  | ownership_header_split_if
                  | exact .refl state
            | some receiving =>
              have bound := (Array.getElem?_eq_some_iff.mp stored).choose
              repeat' first
                | simp only [lookupStorage_result, stored, replaceStorage_result,
                    replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                    ConstructionM.fail, emit_result, ConstructionResult.finalState]
                | ownership_header_split_if
                | exact .refl state
                | exact removed _


theorem removeConstructionHeader_forwardLinks (id : DestinationId)
    (state : ConstructionState) (links : DestinationForwardLinks state) :
    DestinationForwardLinks (removeConstructionHeader id state).finalState := by
  simp only [removeConstructionHeader, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact links
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact links
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          cases progress : destination.progress <;> (try simp only [progress]) <;> try exact links
          case built count =>
            have removed : ∀ storage : ReceivingStorage,
                DestinationForwardLinks { state with
                  storage := state.storage.set! destination.storage storage
                  destinations := state.destinations.set! id { destination with layout := .elements, writeEnd := destination.writeEnd - 4 },
                  events := state.events ++ [.relocate id .headerRemoval] } := by
              intro storage
              exact destinationForwardLinks_replace_leaf state id destination _ present rfl rfl (by simp [OwnershipLeafProgress, progress]) links
            simp only [progress] at removed
            cases stored : state.storage[destination.storage]? with
            | none =>
                repeat' first
                  | simp only [lookupStorage_result, stored, bind, ConstructionM.fail,
                      ConstructionResult.finalState]
                  | ownership_header_split_if
                  | exact links
            | some receiving =>
              have bound := (Array.getElem?_eq_some_iff.mp stored).choose
              repeat' first
                | simp only [lookupStorage_result, stored, replaceStorage_result,
                    replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                    ConstructionM.fail, emit_result, ConstructionResult.finalState]
                | ownership_header_split_if
                | exact links
                | exact removed _


theorem prepareNamedBinding_ownership_rows (id : DestinationId)
    (localType : Construct.Ty) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    OwnershipLinkRowsFrame state (prepareNamedBinding id localType state).finalState := by
  simp only [prepareNamedBinding, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have bound := (valid.2.2.1 id destination present).1
          cases progress : destination.progress <;> (try simp only [progress]) <;> try exact .refl state
          case «open» count =>
            cases count <;> try exact .refl state
            case zero =>
              have prepared : ∀ (storage : Array ReceivingStorage), storage.size = state.storage.size →
                  ∀ (layout : ReceivingLayout) (writeEnd : Nat),
                  OwnershipLinkRowsFrame state { state with storage := storage, destinations := state.destinations.set! id { destination with capability := { destination.capability with logicalType := localType }, layout := layout, writeEnd := writeEnd } } := by
                intro storage size layout writeEnd
                refine ownershipLinkRowsFrame_replace_mutable state id destination _ present ?_ ?_ ?_
                · rfl
                · cases use : destination.use <;> simp [OwnershipLinkBacking, use]
                · simp [progress, ReservationStableProgress]
              simp only [progress] at prepared
              cases stored : state.storage[destination.storage]?
              all_goals
                repeat' first
                  | simp only [lookupStorage_result, stored, replaceStorage_result,
                      replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                      ConstructionM.fail, emit_result, ConstructionResult.finalState]
                  | ownership_header_split_if
                  | exact .refl state
                  | exact prepared _ (by simp) _ _


theorem prepareNamedBinding_forwardLinks (id : DestinationId)
    (localType : Construct.Ty) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) (links : DestinationForwardLinks state) :
    DestinationForwardLinks (prepareNamedBinding id localType state).finalState := by
  simp only [prepareNamedBinding, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact links
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact links
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have bound := (valid.2.2.1 id destination present).1
          cases progress : destination.progress <;> (try simp only [progress]) <;> try exact links
          case «open» count =>
            cases count <;> try exact links
            case zero =>
              have prepared : ∀ (storage : Array ReceivingStorage), storage.size = state.storage.size →
                  ∀ (layout : ReceivingLayout) (writeEnd : Nat),
                  DestinationForwardLinks { state with storage := storage, destinations := state.destinations.set! id { destination with capability := { destination.capability with logicalType := localType }, layout := layout, writeEnd := writeEnd } } := by
                intro storage size layout writeEnd
                exact destinationForwardLinks_replace_leaf state id destination _ present rfl rfl (by simp [OwnershipLeafProgress, progress]) links
              simp only [progress] at prepared
              cases stored : state.storage[destination.storage]?
              all_goals
                repeat' first
                  | simp only [lookupStorage_result, stored, replaceStorage_result,
                      replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                      ConstructionM.fail, emit_result, ConstructionResult.finalState]
                  | ownership_header_split_if
                  | exact links
                  | exact prepared _ (by simp) _ _


theorem truncateConstructionStorage_ownership_rows (storageId : StorageId)
    (start finish count : Nat) (owner : Option DestinationId) (retainSlots : Bool)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    OwnershipLinkRowsFrame state
      (truncateConstructionStorage storageId start finish count owner retainSlots state).finalState := by
  simp only [truncateConstructionStorage, lookupStorage_result, bind]
  cases stored : state.storage[storageId]? with
  | none => exact .refl state
  | some storage =>
      simp only [stored]
      have bound := (Array.getElem?_eq_some_iff.mp stored).choose
      have storageChanged : ∀ value : ReceivingStorage,
          OwnershipLinkRowsFrame state { state with storage := state.storage.set! storageId value } := by
        intro value
        exact .refl state
      cases owner with
      | none =>
          repeat' first
            | simp only [ConstructionM.get, replaceStorage_result, bound, ↓reduceIte,
                bind, pure, ConstructionM.fail, ConstructionResult.finalState]
            | ownership_header_split_if
            | exact .refl state
            | exact storageChanged _
      | some id =>
          cases present : state.destinations[id]? with
          | none =>
              repeat' first
                | simp only [ConstructionM.get, writableDestination_result, present,
                    ↓reduceIte, bind, pure, ConstructionM.fail, ConstructionResult.finalState]
                | ownership_header_split_if
                | exact .refl state
          | some destination =>
              cases allowed : destinationCanWrite state id with
              | false =>
                  repeat' first
                    | simp only [ConstructionM.get, writableDestination_result, present, allowed,
                        ↓reduceIte, bind, pure, ConstructionM.fail, ConstructionResult.finalState]
                    | ownership_header_split_if
                    | exact .refl state
              | true =>
                  have inside := (Array.getElem?_eq_some_iff.mp present).choose
                  have capId := valid.2.1 id destination present
                  cases progress : destination.progress <;> (try simp only [progress])
                  all_goals
                    try solve | repeat' first
                      | simp only [ConstructionM.get, writableDestination_result, present, allowed,
                          progress, ↓reduceIte, bind, pure, ConstructionM.fail, ConstructionResult.finalState]
                      | ownership_header_split_if
                      | exact .refl state
                  case built oldCount =>
                    have truncated : ∀ value : ReceivingStorage,
                        OwnershipLinkRowsFrame state { state with storage := state.storage.set! storageId value, destinations := state.destinations.set! id { destination with progress := .built count, writeEnd := finish } } := by
                      intro value
                      refine ownershipLinkRowsFrame_replace_mutable state id destination _ present ?_ ?_ ?_
                      · rfl
                      · cases use : destination.use <;> simp [OwnershipLinkBacking, use]
                      · simp [progress, ReservationStableProgress]
                    repeat' first
                      | simp only [ConstructionM.get, writableDestination_result, present, allowed,
                          progress, capId, replaceStorage_result, replaceDestination_result,
                          bound, inside, ↓reduceIte, bind, pure, ConstructionM.fail,
                          ConstructionResult.finalState]
                      | ownership_header_split_if
                      | exact .refl state
                      | exact truncated _


theorem truncateConstructionStorage_forwardLinks (storageId : StorageId)
    (start finish count : Nat) (owner : Option DestinationId) (retainSlots : Bool)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) (links : DestinationForwardLinks state) :
    DestinationForwardLinks
      (truncateConstructionStorage storageId start finish count owner retainSlots state).finalState := by
  simp only [truncateConstructionStorage, lookupStorage_result, bind]
  cases stored : state.storage[storageId]? with
  | none => exact links
  | some storage =>
      simp only [stored]
      have bound := (Array.getElem?_eq_some_iff.mp stored).choose
      have storageChanged : ∀ value : ReceivingStorage,
          DestinationForwardLinks { state with storage := state.storage.set! storageId value } := by
        intro value
        exact links
      cases owner with
      | none =>
          repeat' first
            | simp only [ConstructionM.get, replaceStorage_result, bound, ↓reduceIte,
                bind, pure, ConstructionM.fail, ConstructionResult.finalState]
            | ownership_header_split_if
            | exact links
            | exact storageChanged _
      | some id =>
          cases present : state.destinations[id]? with
          | none =>
              repeat' first
                | simp only [ConstructionM.get, writableDestination_result, present,
                    ↓reduceIte, bind, pure, ConstructionM.fail, ConstructionResult.finalState]
                | ownership_header_split_if
                | exact links
          | some destination =>
              cases allowed : destinationCanWrite state id with
              | false =>
                  repeat' first
                    | simp only [ConstructionM.get, writableDestination_result, present, allowed,
                        ↓reduceIte, bind, pure, ConstructionM.fail, ConstructionResult.finalState]
                    | ownership_header_split_if
                    | exact links
              | true =>
                  have inside := (Array.getElem?_eq_some_iff.mp present).choose
                  have capId := valid.2.1 id destination present
                  cases progress : destination.progress <;> (try simp only [progress])
                  all_goals
                    try solve | repeat' first
                      | simp only [ConstructionM.get, writableDestination_result, present, allowed,
                          progress, ↓reduceIte, bind, pure, ConstructionM.fail, ConstructionResult.finalState]
                      | ownership_header_split_if
                      | exact links
                  case built oldCount =>
                    have truncated : ∀ value : ReceivingStorage,
                        DestinationForwardLinks { state with storage := state.storage.set! storageId value, destinations := state.destinations.set! id { destination with progress := .built count, writeEnd := finish } } := by
                      intro value
                      exact destinationForwardLinks_replace_leaf state id destination _ present rfl rfl (by simp [OwnershipLeafProgress, progress]) links
                    repeat' first
                      | simp only [ConstructionM.get, writableDestination_result, present, allowed,
                          progress, capId, replaceStorage_result, replaceDestination_result,
                          bound, inside, ↓reduceIte, bind, pure, ConstructionM.fail,
                          ConstructionResult.finalState]
                      | ownership_header_split_if
                      | exact links
                      | exact truncated _

end Goose.Proofs.ConstructionExecutionOwnership
