import Goose.Proofs.ConstructionRootCorrespondenceWrites

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem bindRoot_counters (root : Goose.Core.RootInst) (value : Value) (before after : ExecutionState)
    (bound : bindRoot root value before = .ok () after) :
    after.nextAct = before.nextAct ∧ after.nextScope = before.nextScope := by
  cases ordinal : before.objectOrdinals.lookup root <;> cases value <;>
    simp only [bindRoot, bind, EvalM.get, ordinal, Option.isNone, Bool.false_eq_true, ite_false,
      ite_true, setObjectOrdinal, EvalM.set, pure, reserveRootObject,
      liftConstruction, reserveStorage, ConstructionM.get, ConstructionM.set, bindStaticRoot] at bound <;>
    cases bound <;> exact ⟨rfl, rfl⟩

#print axioms bindRoot_counters
end Goose.Proofs.ConstructionAcceptedExecution
