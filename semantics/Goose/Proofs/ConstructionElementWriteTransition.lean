import Goose.Construct.Destination
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionStorage
open Goose.Construct Goose.Core

inductive ElementWriteTransition (id : DestinationId) (bytes : ByteArray) (state : ConstructionState) :
    ConstructionResult Unit → Prop
  | rejected (reason : ConstructionFault) : ElementWriteTransition id bytes state (.fault reason state)
  | written (destination : PendingDestination) (storage : ReceivingStorage) (count : Nat)
      (present : state.destinations[id]? = some destination)
      (stored : state.storage[destination.storage]? = some storage)
      (opened : destination.progress = .open count) :
      ElementWriteTransition id bytes state (.ok () { state with
        storage := state.storage.set! destination.storage { storage with bytes := (
          storage.bytes.extract 0 destination.writeEnd ++ bytes ++
            storage.bytes.extract (destination.writeEnd + bytes.size) storage.bytes.size) }
        destinations := state.destinations.set! id { destination with
          progress := .open (count + 1), writeEnd := destination.writeEnd + bytes.size }
        events := state.events ++ [.write id count] })

local syntax "element_write_split_if" : tactic
elab_rules : tactic
  | `(tactic| element_write_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no element write condition"
      return [yes.mvarId, no.mvarId]

set_option maxHeartbeats 800000 in
theorem writeElement_transition (id : DestinationId) (bytes : ByteArray) (state : ConstructionState) :
    ElementWriteTransition id bytes state (writeElement id bytes state) := by
  simp only [writeElement, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .rejected .destination
  | some destination =>
      cases allowed : destinationCanWrite state id with
      | false => exact .rejected .protocol
      | true =>
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          cases progress : destination.progress <;> (try simp only [progress]) <;>
            try exact .rejected .protocol
          case «open» count =>
            cases stored : state.storage[destination.storage]? with
            | none => simp only [lookupStorage_result, stored, bind]; exact .rejected .storage
            | some storage =>
                have committed : ElementWriteTransition id bytes state (.ok () { state with
                    storage := state.storage.set! destination.storage { storage with bytes := (
                      storage.bytes.extract 0 destination.writeEnd ++ bytes ++
                        storage.bytes.extract (destination.writeEnd + bytes.size) storage.bytes.size) }
                    destinations := state.destinations.set! id { destination with
                      progress := .open (count + 1), writeEnd := destination.writeEnd + bytes.size }
                    events := state.events ++ [.write id count] }) :=
                  .written destination storage count present stored progress
                have bound := (Array.getElem?_eq_some_iff.mp stored).1
                simp only [lookupStorage_result, stored, bind]
                element_write_split_if
                · exact .rejected .capacity
                · try simp only [pure, bind, ConstructionM.fail]
                  cases layout : (destination.adaptation.map (·.layout)).getD destination.layout <;>
                    simp only [layout]
                  all_goals
                    repeat' first
                      | simp only [pure, bind, ConstructionM.fail]
                      | element_write_split_if
                    all_goals try exact .rejected _
                    all_goals
                      cases use : destination.use <;> simp only [use]
                      all_goals
                        try solve | repeat' first
                            | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                ConstructionM.fail, emit_result]
                            | element_write_split_if
                            | exact .rejected _
                            | exact committed
                      case child parentId =>
                        cases parentFound : state.destinations[parentId]? with
                        | none => simp [lookupDestination_result, parentFound, bind]; exact .rejected _
                        | some parent =>
                          simp only [lookupDestination_result, parentFound, bind]
                          cases parentLayout : parent.layout <;> (try simp only [parentLayout])
                          all_goals
                            try solve | repeat' first
                                | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                    replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                    ConstructionM.fail, emit_result]
                                | element_write_split_if
                                | exact .rejected _
                                | exact committed
                          case limited capacity slotBytes =>
                            cases parentProgress : parent.progress <;> (try simp only [parentProgress])
                            all_goals
                              try solve | repeat' first
                                  | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                      replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                      ConstructionM.fail, emit_result]
                                  | element_write_split_if
                                  | exact .rejected _
                                  | exact committed
                            case suspended parentCount child =>
                              cases parentBacking : parent.backing <;> (try simp only [parentBacking])
                              all_goals
                                try solve | repeat' first
                                    | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                        replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                        ConstructionM.fail, emit_result]
                                    | element_write_split_if
                                    | exact .rejected _
                                    | exact committed
                              case direct parentStorage =>
                                cases backing : destination.backing <;> (try simp only [backing])
                                all_goals
                                  repeat' first
                                    | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                        replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                        ConstructionM.fail, emit_result]
                                    | element_write_split_if
                                    | exact .rejected _
                                    | exact committed

theorem writeElement_success_destination (id : DestinationId) (bytes : ByteArray)
    (before after : ConstructionState) (destination : PendingDestination) (count : Nat)
    (present : before.destinations[id]? = some destination)
    (opened : destination.progress = .open count)
    (executed : writeElement id bytes before = .ok () after) :
    after.destinations[id]? = some { destination with
      progress := .open (count + 1), writeEnd := destination.writeEnd + bytes.size } ∧
      after.destinationSuccessors = before.destinationSuccessors := by
  have transition := writeElement_transition id bytes before
  rw [executed] at transition
  cases transition with
  | written actual storage actualCount actualPresent actualStored actualOpened =>
      have same := Option.some.inj (actualPresent.symm.trans present)
      subst actual
      have sameCount := DestinationProgress.open.inj (actualOpened.symm.trans opened)
      subst actualCount
      have inside := (Array.getElem?_eq_some_iff.mp present).1
      exact ⟨Array.getElem?_setIfInBounds_self_of_lt inside, rfl⟩

theorem writeElement_preserves_indexing (id : DestinationId) (bytes : ByteArray) (state : ConstructionState) :
    (writeElement id bytes state).finalState.destinations.size = state.destinations.size ∧
      (writeElement id bytes state).finalState.destinationSuccessors = state.destinationSuccessors := by
  have transition := writeElement_transition id bytes state
  generalize evaluated : writeElement id bytes state = result at transition ⊢
  cases transition <;> simp [ConstructionResult.finalState]

#print axioms writeElement_transition
#print axioms writeElement_success_destination
#print axioms writeElement_preserves_indexing

end Goose.Proofs.ConstructionStorage
