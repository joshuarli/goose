import Goose.Proofs.Exit

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

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

#print axioms bindRoot_events
#print axioms rootOf_unchanged
end Goose.Proofs.ConstructionAcceptedExecution
