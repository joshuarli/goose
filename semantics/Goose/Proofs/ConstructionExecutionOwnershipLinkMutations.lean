import Goose.Proofs.ConstructionExecutionOwnershipLinks
import Goose.Proofs.ConstructionExecutionProtocolQueries
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

local syntax "ownership_mutation_split_if" : tactic
elab_rules : tactic
  | `(tactic| ownership_mutation_split_if) =>
      Lean.Elab.Tactic.liftMetaTactic fun goal => do
        let some (yes, no) ← Lean.Meta.splitIfTarget? goal
          | Lean.throwError "no ownership mutation condition to split"
        return [yes.mvarId, no.mvarId]

def OwnershipLeafProgress : DestinationProgress → Prop
  | .suspended _ _ | .exiting _ _ => False
  | _ => True

theorem destinationForwardLinks_replace_leaf (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (sameBacking : after.backing = before.backing)
    (leaf : OwnershipLeafProgress after.progress) (valid : DestinationForwardLinks state) :
    DestinationForwardLinks { state with destinations := state.destinations.set! id after } := by
  apply destinationForwardLinks_replace state id before after present sameUse sameBacking valid
  cases progress : after.progress <;> simp_all [OwnershipLeafProgress, DestinationForwardLink]

theorem destinationForwardLinks_replace_metadata (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (sameBacking : after.backing = before.backing)
    (sameProgress : after.progress = before.progress) (valid : DestinationForwardLinks state) :
    DestinationForwardLinks { state with destinations := state.destinations.set! id after } := by
  apply destinationForwardLinks_replace state id before after present sameUse sameBacking valid
  have previous := valid id before present
  cases progress : before.progress <;>
    simpa [DestinationForwardLink, sameProgress, progress, PendingDestination.storage, sameBacking] using previous

theorem adaptDestinationType_forwardLinks (state : ConstructionState) (id : DestinationId)
    (ty : Construct.Ty) (valid : DestinationForwardLinks state) :
    DestinationForwardLinks (adaptDestinationType id ty state).finalState := by
  simp only [adaptDestinationType, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some row =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact valid
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          cases progress : row.progress <;> try simp only [progress] <;> try exact valid
          all_goals
            repeat' first
              | exact valid
              | solve
                | exact destinationForwardLinks_replace_metadata state id row _ present rfl rfl (by simpa only [progress]) valid
              | simp only [replaceDestination_result, inside, ↓reduceIte, bind, pure,
                  ConstructionM.fail, ConstructionResult.finalState]
              | ownership_mutation_split_if
              | split

set_option maxHeartbeats 1000000 in
theorem finishDestination_forwardLinks (state : ConstructionState) (id : DestinationId)
    (bounded : DestinationLifecycleInvariant state) (valid : DestinationForwardLinks state) :
    DestinationForwardLinks (finishDestination id state).finalState := by
  simp only [finishDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some row =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact valid
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          have storageInside := (bounded.2.2.1 id row present).1
          cases progress : row.progress <;> try simp only [progress] <;> try exact valid
          case «open» count =>
            have finished := destinationForwardLinks_replace_leaf state id row
              { row with progress := .built count } present rfl rfl (by trivial) valid
            have storedFinished : ∀ storage : ReceivingStorage,
                DestinationForwardLinks { state with
                  storage := state.storage.set! row.storage storage
                  destinations := state.destinations.set! id { row with progress := .built count } } :=
              fun _ => finished
            cases layout : row.layout <;> simp only [layout]
            all_goals
              simp only [layout] at finished storedFinished
              cases stored : state.storage[row.storage]?
              all_goals
                repeat' first
                  | exact valid
                  | exact finished
                  | exact storedFinished _
                  | simp only [lookupStorage_result, stored, replaceStorage_result,
                      replaceDestination_result, inside, storageInside, ↓reduceIte, pure, bind,
                      ConstructionM.fail, ConstructionResult.finalState]
                  | ownership_mutation_split_if
                  | split

theorem abandonDestination_forwardLinks (state : ConstructionState) (id : DestinationId)
    (valid : DestinationForwardLinks state) :
    DestinationForwardLinks (abandonDestination id state).finalState := by
  simp only [abandonDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some row =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact valid
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          cases progress : row.progress <;> try simp only [progress] <;> try exact valid
          all_goals
            simp only [lookupStorage_result, bind]
            cases stored : state.storage[row.storage]? with
            | none => exact valid
            | some storage =>
                have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
                simp only [stored, replaceStorage_result, replaceDestination_result,
                  storageInside, inside, ↓reduceIte, bind, pure, emit_result,
                  ConstructionResult.finalState]
                exact destinationForwardLinks_replace_leaf state id row
                  { row with progress := .abandoned } present rfl rfl (by trivial) valid

set_option maxHeartbeats 1000000 in
theorem stageDestination_forwardLinks (state : ConstructionState) (id : DestinationId)
    (valid : DestinationForwardLinks state) :
    DestinationForwardLinks (stageDestination id state).finalState := by
  simp only [stageDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some row =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact valid
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          cases progress : row.progress <;> try simp only [progress] <;> try exact valid
          case «open» count =>
            cases count <;> try simp only <;> try exact valid
            cases layout : row.layout <;> try simp only [layout] <;> try exact valid
            cases backing : row.backing <;> try simp only [backing] <;> try exact valid
            cases known : row.knownCount <;> try simp only [known] <;> try exact valid
            cases use : row.use <;> try simp only [use] <;> try exact valid
            repeat' first
              | solve
                | simp only [← progress, ← layout, ← known, ← use]
                  exact destinationForwardLinks_replace_sources state id row _ present rfl
                    (by simp [OwnershipLinkBacking, use]) valid
                    (by simp [DestinationForwardLink, progress])
              | simp only [reserveStorage, ConstructionM.get, ConstructionM.set, replaceDestination_result,
                  inside, ↓reduceIte, emit_result, bind, pure, ConstructionResult.finalState]
              | ownership_mutation_split_if
              | split

end Goose.Proofs.ConstructionExecutionOwnership
