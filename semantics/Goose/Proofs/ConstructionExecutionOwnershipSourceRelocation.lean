import Goose.Proofs.ConstructionExecutionOwnershipSourceMutations
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

local syntax "ownership_source_relocation_split_if" : tactic
elab_rules : tactic
  | `(tactic| ownership_source_relocation_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no relocation condition to split"
      return [yes.mvarId, no.mvarId]

local syntax "ownership_source_relocation_split_match" : tactic
elab_rules : tactic
  | `(tactic| ownership_source_relocation_split_match) => Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
      let target ← Lean.instantiateMVars (← goal.getType)
      let mut excluded : Lean.ExprSet := {}
      repeat
        let some expression ← Lean.Meta.findSplit? target .match excluded
          | Lean.throwError "no concrete relocation match to split"
        let some application ← Lean.Meta.matchMatcherApp? expression
          | Lean.throwError "expected relocation match"
        let abstractState ← application.discrs.anyM fun discriminant => do
          let type ← Lean.Meta.whnf (← Lean.Meta.inferType discriminant)
          return type.getAppFn.isConstOf ``ConstructionResult
        if abstractState then
          excluded := excluded.insert expression
        else
          try
            let some discriminant ← application.discrs.findM? (fun value => return !(← Lean.Meta.isConstructorApp value))
              | Lean.throwError "relocation match is already concrete"
            let (variables, generalized) ← goal.generalize #[{ expr := discriminant, hName? := some `relocationCase }]
            return (← generalized.cases variables[0]!).toList.map (·.mvarId)
          catch _ =>
            excluded := excluded.insert expression

private theorem fit_commit_source (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (count receiver stage start finish rollback : Nat)
    (storage : Array ReceivingStorage) (size : storage.size = state.storage.size)
    (present : state.destinations[id]? = some destination)
    (progress : destination.progress = .built count)
    (backing : destination.backing = .staged receiver stage)
    (receiving : destination.use = .receiver ∨ ∃ parent, destination.use = .child parent)
    (valid : DestinationLifecycleInvariant state) :
    OwnershipSourceExtension state { state with
      storage := storage
      destinations := state.destinations.set! id { destination with
        backing := .direct receiver
        capability := { destination.capability with start := start }
        writeEnd := finish
        rollbackEnd := rollback }
      events := state.events ++ [.copy (.storage stage []) id] } := by
  refine ownershipSourceExtension_replace state id destination _ present ?_ ?_
  · rfl
  · cases use : destination.use <;> simp_all [OwnershipLinkBacking, DestinationBacking.receiverStorage]



set_option maxHeartbeats 2000000 in
theorem fitStagedDestination_ownership_source (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    OwnershipSourceExtension state (fitStagedDestination id state).finalState := by
  simp only [fitStagedDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          cases progress : destination.progress <;> try simp only [progress] <;> try exact .refl state
          case built count =>
            cases backing : destination.backing <;> try simp only [backing] <;> try exact .refl state
            case staged receiver stage =>
              have receiverInside : receiver < state.storage.size := by
                simpa only [backing, DestinationBacking.receiverStorage] using (valid.2.2.1 id destination present).2
              have stageInside : stage < state.storage.size := by
                simpa only [PendingDestination.storage, backing, DestinationBacking.writeStorage] using
                  (valid.2.2.1 id destination present).1
              cases receiverResult : state.storage[receiver]?
              all_goals cases stageResult : state.storage[stage]?
              all_goals cases use : destination.use
              all_goals cases layout : destination.layout
              all_goals repeat' first
                | exact .refl state
                | solve
                  | simp only [← layout, ← use, ← backing, ← progress]
                    apply fit_commit_source state id destination count receiver stage _ _ _ _ _ present progress backing
                    · first | exact Or.inl use | exact Or.inr ⟨_, use⟩
                    · exact valid
                    · simp [Array.set!_eq_setIfInBounds]
                | simp only [lookupStorage_result, writableDestination_result,
                    ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                    replaceDestination_result, replaceStorage_result, emit_result,
                    inside, receiverInside, stageInside, receiverResult, stageResult, use, layout,
                    Array.size_set!, ↓reduceIte, bind, pure, ConstructionResult.finalState]
                | ownership_source_relocation_split_match
                | ownership_source_relocation_split_if


end Goose.Proofs.ConstructionExecutionOwnership
