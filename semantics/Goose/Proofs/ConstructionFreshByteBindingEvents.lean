import Goose.Proofs.ConstructionFreshByteValueEvents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem storedDestination_events (id : Nat) (state : ExecutionState) :
    (Goose.Proofs.Exit.stepState (storedDestination id state)).construction.events = state.construction.events := by
  simp only [storedDestination, getDestination, EvalM.get, bind]
  cases found : state.construction.destinations[id]? with
  | none => simp [found, Goose.Construct.fault, EvalM.stop, Goose.Proofs.Exit.stepState]
  | some row =>
    cases progress : row.progress <;>
      simp [found, progress, progressCount, Goose.Construct.fault, EvalM.stop, pure, bind, Goose.Proofs.Exit.stepState]

theorem bindRoot_events (root : Goose.Core.RootInst) (value : Value) (state : ExecutionState) :
    (Goose.Proofs.Exit.stepState (bindRoot root value state)).construction.events = state.construction.events := by
  cases lookup : state.objectOrdinals.lookup root <;> cases value <;>
    simp [bindRoot, EvalM.get, bind, pure, bindStaticRoot, setObjectOrdinal, EvalM.set,
      reserveRootObject, lookup, liftConstruction, reserveStorage, ConstructionM.get, ConstructionM.set,
      Goose.Proofs.Exit.stepState]

theorem rootOf_unchanged (environment : RuntimeActivation) (id : Nat) (state : ExecutionState) :
    (Goose.Proofs.Exit.stepState (rootOf environment id state)) = state := by
  cases declared : environment.vars[id]? with
  | none => simp [rootOf, declared, Goose.Construct.fault, EvalM.stop, Goose.Proofs.Exit.stepState]
  | some descriptor =>
    cases scope : environment.scopes.find? (fun entry => entry.1 == descriptor.scope) with
    | none => simp [rootOf, declared, scope, Goose.Construct.fault, EvalM.stop, Goose.Proofs.Exit.stepState]
    | some found => cases found; simp [rootOf, declared, scope, pure, Goose.Proofs.Exit.stepState]

theorem eval_bind_assoc (action : EvalM α) (next : α → EvalM β) (last : β → EvalM γ) :
    (action >>= next) >>= last = action >>= fun value => next value >>= last := by
  funext state
  simp only [bind]
  cases action state <;> rfl

theorem eval_pure_bind (value : α) (next : α → EvalM β) :
    pure value >>= next = next value := rfl

theorem bind_events_frame (action : EvalM α) (next : α → EvalM β) (state : ExecutionState)
    (preserves : ∀ value current,
      (Goose.Proofs.Exit.stepState (next value current)).construction.events = current.construction.events) :
    (Goose.Proofs.Exit.stepState ((action >>= next) state)).construction.events =
      (Goose.Proofs.Exit.stepState (action state)).construction.events := by
  cases executed : action state with
  | ok value after => simpa only [bind, executed, Goose.Proofs.Exit.stepState] using preserves value after
  | stop reason after => simp only [bind, executed, Goose.Proofs.Exit.stepState]
  | escape target carriers after => simp only [bind, executed, Goose.Proofs.Exit.stepState]
  | jump target kind after => simp only [bind, executed, Goose.Proofs.Exit.stepState]

#print axioms bind_events_frame
#print axioms storedDestination_events
#print axioms bindRoot_events
#print axioms rootOf_unchanged

end Goose.Proofs.ConstructionAcceptedExecution
