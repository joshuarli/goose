import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataUpdates
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

local syntax "protocol_split_if" : tactic
elab_rules : tactic
  | `(tactic| protocol_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no reservation condition to split"
      return [yes.mvarId, no.mvarId]

theorem finishDestination_reservation_frame (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (finishDestination id state).finalState := by
  simp only [finishDestination, writableDestination_result, bind]
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
            have changed : ∀ (after : PendingDestination) (storage : Array ReceivingStorage),
                state.storage.size ≤ storage.size → ReservationMetadataFrame state
                  { state with storage := storage, destinations := state.destinations.set! id after } := by
              intro after storage size
              simpa only [List.append_nil] using reservationMetadataFrame_replace_mutable
                state id destination after storage [] present size
                (by simp [progress, ReservationStableProgress])
                (by intro queried different; rfl)
            have finished := changed { destination with progress := .built count } state.storage (Nat.le_refl _)
            have storedFinished := fun storage : ReceivingStorage =>
              changed { destination with progress := .built count }
                (state.storage.set! destination.storage storage) (by simp)
            cases layout : destination.layout <;> simp only [layout]
            all_goals
              simp only [layout] at finished storedFinished
              cases stored : state.storage[destination.storage]?
              all_goals
                repeat' first
                  | simp only [lookupStorage_result, stored, replaceStorage_result,
                      replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                      ConstructionM.fail, ConstructionResult.finalState]
                  | protocol_split_if
                  | exact .refl state
                  | exact finished
                  | exact storedFinished _

theorem removeConstructionHeader_metadata_frame (id : DestinationId)
    (state : ConstructionState) :
    ReservationMetadataFrame state (removeConstructionHeader id state).finalState := by
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
                ReservationMetadataFrame state { state with
                  storage := state.storage.set! destination.storage storage
                  destinations := state.destinations.set! id { destination with layout := .elements, writeEnd := destination.writeEnd - 4 },
                  events := state.events ++ [.relocate id .headerRemoval] } := by
              intro storage
              apply reservationMetadataFrame_replace_mutable state id destination _ _ _ present
              · simp
              · simp [progress, ReservationStableProgress]
              · intro queried different
                simp [destinationObservations, observeDestination, Ne.symm different]
            simp only [progress] at removed
            cases stored : state.storage[destination.storage]? with
            | none =>
                repeat' first
                  | simp only [lookupStorage_result, stored, bind, ConstructionM.fail,
                      ConstructionResult.finalState]
                  | protocol_split_if
                  | exact .refl state
            | some receiving =>
              have bound := (Array.getElem?_eq_some_iff.mp stored).choose
              repeat' first
                | simp only [lookupStorage_result, stored, replaceStorage_result,
                    replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                    ConstructionM.fail, emit_result, ConstructionResult.finalState]
                | protocol_split_if
                | exact .refl state
                | exact removed _

theorem removeConstructionHeader_reservation_frame (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (removeConstructionHeader id state).finalState :=
  removeConstructionHeader_metadata_frame id state

theorem prepareNamedBinding_reservation_frame (id : DestinationId)
    (localType : Construct.Ty) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (prepareNamedBinding id localType state).finalState := by
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
                  ReservationMetadataFrame state { state with storage := storage, destinations := state.destinations.set! id { destination with capability := { destination.capability with logicalType := localType }, layout := layout, writeEnd := writeEnd } } := by
                intro storage size layout writeEnd
                simpa only [List.append_nil] using reservationMetadataFrame_replace_mutable state id destination _ storage []
                  present (Nat.le_of_eq size.symm) (by simp [progress, ReservationStableProgress])
                  (by intro queried different; rfl)
              simp only [progress] at prepared
              cases stored : state.storage[destination.storage]?
              all_goals
                repeat' first
                  | simp only [lookupStorage_result, stored, replaceStorage_result,
                      replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                      ConstructionM.fail, emit_result, ConstructionResult.finalState]
                  | protocol_split_if
                  | exact .refl state
                  | exact prepared _ (by simp) _ _

set_option maxHeartbeats 800000 in
theorem writeElement_reservation_frame (id : DestinationId) (bytes : ByteArray)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (writeElement id bytes state).finalState := by
  simp only [writeElement, writableDestination_result, bind]
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
            have committed : ∀ storage : ReceivingStorage,
                ReservationMetadataFrame state { state with
                  storage := state.storage.set! destination.storage storage
                  destinations := state.destinations.set! id { destination with progress := .open (count + 1), writeEnd := destination.writeEnd + bytes.size },
                  events := state.events ++ [.write id count] } := by
              intro storage
              apply reservationMetadataFrame_replace_mutable state id destination _ _ _ present
              · simp
              · simp [progress, ReservationStableProgress]
              · intro queried different
                simp [destinationObservations, observeDestination, Ne.symm different]
            cases stored : state.storage[destination.storage]? with
            | none => simp only [lookupStorage_result, stored, bind]; exact .refl state
            | some storage =>
                simp only [lookupStorage_result, stored, bind]
                protocol_split_if
                · exact .refl state
                · try simp only [pure, bind, ConstructionM.fail, ConstructionResult.finalState]
                  cases layout : (destination.adaptation.map (·.layout)).getD destination.layout <;>
                    simp only [layout]
                  all_goals
                    repeat' first
                      | simp only [pure, bind, ConstructionM.fail, ConstructionResult.finalState]
                      | protocol_split_if
                    all_goals try exact .refl state
                    all_goals
                      cases use : destination.use <;> simp only [use]
                      all_goals
                        try solve | repeat' first
                            | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                ConstructionM.fail, emit_result, ConstructionResult.finalState]
                            | protocol_split_if
                            | exact .refl state
                            | exact committed _
                      case child parentId =>
                        cases parentFound : state.destinations[parentId]? <;>
                          simp only [lookupDestination_result, parentFound, bind]
                        · repeat' first
                            | simp_all only [↓reduceIte, pure, bind, ConstructionM.fail, ConstructionResult.finalState]
                            | protocol_split_if
                            | exact .refl state
                        · rename_i parent
                          cases parentLayout : parent.layout <;> (try simp only [parentLayout])
                          all_goals
                            try solve | repeat' first
                                | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                    replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                    ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                | protocol_split_if
                                | exact .refl state
                                | exact committed _
                          case limited capacity slotBytes =>
                            cases parentProgress : parent.progress <;> (try simp only [parentProgress])
                            all_goals
                              try solve | repeat' first
                                | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                    replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                    ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                | protocol_split_if
                                | exact .refl state
                                | exact committed _
                            case suspended parentCount child =>
                              cases parentBacking : parent.backing <;> (try simp only [parentBacking])
                              all_goals
                                try solve | repeat' first
                                  | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                      replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                      ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                  | protocol_split_if
                                  | exact .refl state
                                  | exact committed _
                              case direct parentStorage =>
                                cases backing : destination.backing <;> (try simp only [backing])
                                all_goals
                                  repeat' first
                                    | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                        replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                        ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                    | protocol_split_if
                                    | exact .refl state
                                    | exact committed _

theorem truncateConstructionStorage_reservation_frame (storageId : StorageId)
    (start finish count : Nat) (owner : Option DestinationId) (retainSlots : Bool)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state
      (truncateConstructionStorage storageId start finish count owner retainSlots state).finalState := by
  simp only [truncateConstructionStorage, lookupStorage_result, bind]
  cases stored : state.storage[storageId]? with
  | none => exact .refl state
  | some storage =>
      simp only [stored]
      have bound := (Array.getElem?_eq_some_iff.mp stored).choose
      have storageChanged : ∀ value : ReceivingStorage,
          ReservationMetadataFrame state { state with storage := state.storage.set! storageId value } := by
        intro value
        exact reservationMetadataFrame_storage state _ (by simp)
      cases owner with
      | none =>
          repeat' first
            | simp only [ConstructionM.get, replaceStorage_result, bound, ↓reduceIte,
                bind, pure, ConstructionM.fail, ConstructionResult.finalState]
            | protocol_split_if
            | exact .refl state
            | exact storageChanged _
      | some id =>
          cases present : state.destinations[id]? with
          | none =>
              repeat' first
                | simp only [ConstructionM.get, writableDestination_result, present,
                    ↓reduceIte, bind, pure, ConstructionM.fail, ConstructionResult.finalState]
                | protocol_split_if
                | exact .refl state
          | some destination =>
              cases allowed : destinationCanWrite state id with
              | false =>
                  repeat' first
                    | simp only [ConstructionM.get, writableDestination_result, present, allowed,
                        ↓reduceIte, bind, pure, ConstructionM.fail, ConstructionResult.finalState]
                    | protocol_split_if
                    | exact .refl state
              | true =>
                  have inside := (Array.getElem?_eq_some_iff.mp present).choose
                  have capId := valid.2.1 id destination present
                  cases progress : destination.progress <;> (try simp only [progress])
                  all_goals
                    try solve | repeat' first
                      | simp only [ConstructionM.get, writableDestination_result, present, allowed,
                          progress, ↓reduceIte, bind, pure, ConstructionM.fail, ConstructionResult.finalState]
                      | protocol_split_if
                      | exact .refl state
                  case built oldCount =>
                    have truncated : ∀ value : ReceivingStorage,
                        ReservationMetadataFrame state { state with storage := state.storage.set! storageId value, destinations := state.destinations.set! id { destination with progress := .built count, writeEnd := finish } } := by
                      intro value
                      simpa only [List.append_nil] using reservationMetadataFrame_replace_mutable state id destination _ _ [] present
                        (by simp) (by simp [progress, ReservationStableProgress]) (by intro queried different; rfl)
                    repeat' first
                      | simp only [ConstructionM.get, writableDestination_result, present, allowed,
                          progress, capId, replaceStorage_result, replaceDestination_result,
                          bound, inside, ↓reduceIte, bind, pure, ConstructionM.fail,
                          ConstructionResult.finalState]
                      | protocol_split_if
                      | exact .refl state
                      | exact truncated _

#print axioms finishDestination_reservation_frame
#print axioms removeConstructionHeader_reservation_frame
#print axioms prepareNamedBinding_reservation_frame
#print axioms writeElement_reservation_frame
#print axioms truncateConstructionStorage_reservation_frame

end Goose.Proofs.ConstructionExecutionProtocol
