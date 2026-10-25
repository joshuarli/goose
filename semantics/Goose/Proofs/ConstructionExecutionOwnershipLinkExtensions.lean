import Goose.Proofs.ConstructionExecutionOwnershipLinkAllocation
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

local syntax "ownership_extension_split_if" : tactic
elab_rules : tactic
  | `(tactic| ownership_extension_split_if) =>
      Lean.Elab.Tactic.liftMetaTactic fun goal => do
        let some (yes, no) ← Lean.Meta.splitIfTarget? goal
          | Lean.throwError "no ownership extension condition to split"
        return [yes.mvarId, no.mvarId]

set_option maxHeartbeats 2000000 in
theorem openElementExtension_forwardLinks (parentId : DestinationId) (ty : Construct.Ty)
    (layout : ReceivingLayout) (knownCount : Option Nat) (receiver : Core.Loc)
    (state : ConstructionState) (bounded : DestinationLifecycleInvariant state)
    (valid : DestinationForwardLinks state) :
    DestinationForwardLinks (openElementExtension parentId ty layout knownCount receiver state).finalState := by
  simp only [openElementExtension, writableDestination_result, bind]
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
          case built count =>
            simp only [lookupStorage_result, bind]
            cases stored : state.storage[parent.storage]? with
            | none => exact False.elim (Nat.not_le_of_lt storageInside (Array.getElem?_eq_none_iff.mp stored))
            | some receiving =>
                try simp only [stored]
                cases parentLayout : parent.layout <;> cases parentBacking : parent.backing
                all_goals repeat' first
                  | exact valid
                  | solve
                    | simp only [← parentLayout, ← parentBacking]
                      exact destinationForwardLinks_suspend_new_child state parentId count 0 parent _
                        present rfl rfl rfl valid
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      replaceDestination_result, replaceStorage_result, emit_result,
                      Array.size_push, insideAfter, storageInside, stored, parentLayout, parentBacking,
                      ↓reduceIte, bind, pure, ConstructionResult.finalState]
                  | ownership_extension_split_if
                  | split

set_option maxHeartbeats 2000000 in
theorem openExtension_forwardLinks (parentId : DestinationId) (request : ConstructionRequest)
    (knownCount : Option Nat) (state : ConstructionState) (bounded : DestinationLifecycleInvariant state)
    (valid : DestinationForwardLinks state) :
    DestinationForwardLinks (openExtension parentId request knownCount state).finalState := by
  simp only [openExtension, writableDestination_result, bind]
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
          let reserved : ConstructionState := { state with storage := state.storage.push ⟨ByteArray.empty, 0⟩ }
          have reservedValid : DestinationForwardLinks reserved := valid
          cases progress : parent.progress <;> try simp only [progress] <;> try exact valid
          case built count =>
            simp only [pure, lookupStorage_result, bind]
            cases stored : state.storage[parent.storage]? with
            | none => exact valid
            | some receiving =>
                try simp only [stored]
                cases parentLayout : parent.layout <;> cases parentBacking : parent.backing <;> cases knownCount
                all_goals repeat' first
                  | exact valid
                  | exact reservedValid
                  | solve
                    | simp only [← parentLayout, ← parentBacking]
                      exact destinationForwardLinks_suspend_new_child state parentId count 0 parent _
                        present rfl rfl rfl valid
                  | solve
                    | simp only [← parentLayout, ← parentBacking]
                      exact destinationForwardLinks_suspend_new_child reserved parentId count 0 parent _
                        present rfl rfl rfl reservedValid
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      reserveStorage, replaceDestination_result, emit_result,
                      Array.size_push, insideAfter, storageInside, stored, parentLayout, parentBacking,
                      ↓reduceIte, bind, pure, ConstructionResult.finalState, List.append_assoc]
                  | ownership_extension_split_if
                  | split

end Goose.Proofs.ConstructionExecutionOwnership
