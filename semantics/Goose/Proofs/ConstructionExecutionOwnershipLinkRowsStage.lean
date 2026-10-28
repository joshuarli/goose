import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsMutations

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

local syntax "ownership_stage_split_if" : tactic
elab_rules : tactic
  | `(tactic| ownership_stage_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no ownership stage condition to split"
      return [yes.mvarId, no.mvarId]

set_option maxHeartbeats 1000000 in
theorem stageDestination_ownership_rows (state : ConstructionState) (id : DestinationId)
    : OwnershipLinkRowsFrame state (stageDestination id state).finalState := by
  simp only [stageDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some row =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          cases progress : row.progress <;> try simp only [progress] <;> try exact .refl state
          case «open» count =>
            cases count <;> try simp only <;> try exact .refl state
            cases layout : row.layout <;> try simp only [layout] <;> try exact .refl state
            cases backing : row.backing <;> try simp only [backing] <;> try exact .refl state
            cases known : row.knownCount <;> try simp only [known] <;> try exact .refl state
            cases use : row.use <;> try simp only [use] <;> try exact .refl state
            repeat' first
              | solve
                | simp only [← progress, ← layout, ← known, ← use]
                  refine ownershipLinkRowsFrame_replace_mutable state id row _ present ?_ ?_ ?_
                  · rfl
                  · simp [OwnershipLinkBacking, use, backing, DestinationBacking.receiverStorage]
                  · simp [ReservationStableProgress, progress]
              | simp only [reserveStorage, ConstructionM.get, ConstructionM.set, replaceDestination_result,
                  inside, ↓reduceIte, emit_result, bind, pure, ConstructionResult.finalState]
              | ownership_stage_split_if
              | split

end Goose.Proofs.ConstructionExecutionOwnership
