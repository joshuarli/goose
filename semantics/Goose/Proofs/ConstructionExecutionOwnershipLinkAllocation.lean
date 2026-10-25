import Goose.Proofs.ConstructionExecutionOwnershipLinks
import Goose.Proofs.ConstructionExecutionProtocolQueries
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

local syntax "ownership_split_if" : tactic
elab_rules : tactic
  | `(tactic| ownership_split_if) =>
      Lean.Elab.Tactic.liftMetaTactic fun goal => do
        let some (yes, no) ← Lean.Meta.splitIfTarget? goal
          | Lean.throwError "no ownership condition to split"
        return [yes.mvarId, no.mvarId]

theorem openChild_success_parentLink (state final : ConstructionState) (parentId child : DestinationId)
    (ty : Construct.Ty) (layout : ReceivingLayout) (result : openChild parentId ty layout state = .ok child final) :
    ∃ parent count, final.destinations[parentId]? = some parent ∧
      parent.progress = .suspended count child ∧ DestinationForwardLink final parentId parent := by
  simp only [openChild, writableDestination_result, bind] at result
  cases present : state.destinations[parentId]? with
  | none => simp [present] at result
  | some parent =>
      simp only [present] at result
      cases allowed : destinationCanWrite state parentId with
      | false => simp [allowed] at result
      | true =>
          simp only [allowed] at result
          cases progress : parent.progress <;> simp only [progress] at result <;> try contradiction
          case «open» count =>
            simp only [lookupStorage_result, bind] at result
            cases stored : state.storage[parent.storage]? with
            | none => simp [stored] at result
            | some storage =>
                simp only [stored] at result
                have parentInside := (Array.getElem?_eq_some_iff.mp present).1
                have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
                simp only [ConstructionM.get, ConstructionM.set, pure, bind,
                  replaceDestination_result, replaceStorage_result, emit_result,
                  Array.size_push, Nat.lt_succ_of_lt parentInside, storageInside,
                  Array.size_setIfInBounds, ↓reduceIte] at result
                split at result
                · contradiction
                · split at result
                  all_goals
                    simp only [Nat.lt_succ_of_lt parentInside, storageInside, ↓reduceIte, bind, pure] at result
                    cases result
                    refine ⟨{ parent with progress := .suspended count state.destinations.size }, count, ?_, rfl, ?_⟩
                    · simp [Array.set!_eq_setIfInBounds,
                        Array.getElem?_setIfInBounds_self, Nat.lt_succ_of_lt parentInside]
                    · simp [DestinationForwardLink, Array.set!_eq_setIfInBounds,
                        Array.getElem_setIfInBounds, Nat.ne_of_lt parentInside,
                        Array.getElem?_setIfInBounds_ne (Nat.ne_of_lt parentInside),
                        Array.getElem?_push, PendingDestination.storage, DestinationBacking.receiverStorage]

theorem openExitReplacement_success_parentLink (state final : ConstructionState)
    (parentId replacement : DestinationId)
    (result : openExitReplacement parentId state = .ok replacement final) :
    ∃ parent count, final.destinations[parentId]? = some parent ∧
      parent.progress = .exiting count replacement ∧ DestinationForwardLink final parentId parent := by
  simp only [openExitReplacement, writableDestination_result, bind] at result
  cases present : state.destinations[parentId]? with
  | none => simp [present] at result
  | some parent =>
      simp only [present] at result
      cases allowed : destinationCanWrite state parentId with
      | false => simp [allowed] at result
      | true =>
          simp only [allowed] at result
          have parentInside := (Array.getElem?_eq_some_iff.mp present).1
          cases progress : parent.progress <;> simp only [progress, pure, bind] at result <;> try contradiction
          all_goals
            simp only [lookupStorage_result] at result
            cases stored : state.storage[parent.storage]? with
            | none => simp [stored] at result
            | some storage =>
                have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
                simp only [stored, bind, ConstructionM.get, ConstructionM.set, pure,
                  replaceDestination_result, replaceStorage_result, emit_result,
                  Array.size_push, Nat.lt_succ_of_lt parentInside, storageInside,
                  Array.size_setIfInBounds, ↓reduceIte] at result
                split at result
                all_goals
                  simp only [Nat.lt_succ_of_lt parentInside, storageInside, ↓reduceIte, bind, pure] at result
                  cases result
                  simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self,
                    Nat.lt_succ_of_lt parentInside, DestinationForwardLink,
                    Array.getElem_setIfInBounds, Nat.ne_of_lt parentInside,
                    Array.getElem?_setIfInBounds_ne (Nat.ne_of_lt parentInside),
                    Array.getElem?_push]

theorem openChild_forwardLinks_all_outcomes (state : ConstructionState)
    (parentId : DestinationId) (ty : Construct.Ty) (layout : ReceivingLayout)
    (bounded : DestinationLifecycleInvariant state) (valid : DestinationForwardLinks state) :
    DestinationForwardLinks (openChild parentId ty layout state).finalState := by
  simp only [openChild, writableDestination_result, bind]
  cases present : state.destinations[parentId]? with
  | none => exact valid
  | some parent =>
      simp only [present]
      cases allowed : destinationCanWrite state parentId with
      | false => exact valid
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          have insideAfter := Nat.lt_succ_of_lt inside
          have storageInside := (bounded.2.2.1 parentId parent present).1
          cases progress : parent.progress <;> try simp only [progress] <;> try exact valid
          case «open» count =>
            simp only [lookupStorage_result, bind]
            cases stored : state.storage[parent.storage]? with
            | none => exact valid
            | some receiving =>
                simp only [stored]
                repeat' first
                  | exact valid
                  | solve
                    | exact destinationForwardLinks_suspend_new_child state parentId count 0 parent _
                        present rfl rfl rfl valid
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      replaceDestination_result, replaceStorage_result, emit_result,
                      Array.size_push, insideAfter, storageInside, ↓reduceIte,
                      bind, pure, ConstructionResult.finalState]
                  | ownership_split_if
                  | split

theorem openExitReplacement_forwardLinks_all_outcomes (state : ConstructionState)
    (parentId : DestinationId) (bounded : DestinationLifecycleInvariant state)
    (valid : DestinationForwardLinks state) :
    DestinationForwardLinks (openExitReplacement parentId state).finalState := by
  simp only [openExitReplacement, writableDestination_result, bind]
  cases present : state.destinations[parentId]? with
  | none => exact valid
  | some parent =>
      simp only [present]
      cases allowed : destinationCanWrite state parentId with
      | false => exact valid
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          have insideAfter := Nat.lt_succ_of_lt inside
          have storageInside := (bounded.2.2.1 parentId parent present).1
          cases progress : parent.progress <;> try simp only [progress] <;> try exact valid
          all_goals
            try simp only [pure, bind]
            simp only [lookupStorage_result, bind]
            cases stored : state.storage[parent.storage]? with
            | none => exact valid
            | some receiving =>
                simp only [stored]
                repeat' first
                  | exact valid
                  | solve
                    | exact destinationForwardLinks_exit_new_replacement state parentId _ 0 parent _
                        present rfl rfl rfl valid
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      replaceDestination_result, replaceStorage_result, emit_result,
                      Array.size_push, insideAfter, storageInside, ↓reduceIte,
                      bind, pure, ConstructionResult.finalState]
                  | ownership_split_if
                  | split

end Goose.Proofs.ConstructionExecutionOwnership
