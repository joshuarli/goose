import Goose.Proofs.ConstructionExecutionProtocolWrites

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

local syntax "adaptation_split_if" : tactic
elab_rules : tactic
  | `(tactic| adaptation_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no adaptation condition to split"
      return [yes.mvarId, no.mvarId]

private theorem adapt_commit_lifecycle (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (storage : Array ReceivingStorage)
    (present : state.destinations[id]? = some before)
    (size : storage.size = state.storage.size)
    (capability : after.capability.id = before.capability.id)
    (backing : after.backing = before.backing) (use : after.use = before.use)
    (progress : after.progress = before.progress)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with
      storage := storage
      destinations := state.destinations.set! id after} := by
  exact destinationLifecycleInvariant_replace_silent state id before after storage present size
    capability backing use
    (by intro phase matched
        simpa only [DestinationTracePhase.matchesDestination, progress, backing, use] using matched) valid

set_option maxHeartbeats 1000000 in
theorem adaptConstructionDestination_destination_lifecycle_invariant (id : DestinationId)
    (producerType : Construct.Ty) (request : ConstructionRequest)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (adaptConstructionDestination id producerType request state).finalState := by
  simp only [adaptConstructionDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact valid
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have storageInside := (valid.2.2.1 id destination present).1
          cases progress : destination.progress <;> try simp only [progress] <;> try exact valid
          case «open» count =>
            cases count with
            | succ count => exact valid
            | zero =>
                cases stored : state.storage[destination.storage]?
                all_goals repeat' first
                  | exact valid
                  | solve
                    | apply adapt_commit_lifecycle state id destination _ _ present
                      · simp [Array.set!_eq_setIfInBounds]
                      · rfl
                      · rfl
                      · rfl
                      · simp only [progress]
                      · exact valid
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      lookupStorage_result, replaceDestination_result, replaceStorage_result,
                      inside, storageInside, stored, ↓reduceIte, bind, pure, ConstructionResult.finalState]
                  | adaptation_split_if
                  | split

end Goose.Proofs.ConstructionExecutionProtocol
