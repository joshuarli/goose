import Goose.Proofs.ConstructionAcceptedTwoArgumentRoots

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem rpArgs_byValue_cons (environment : PEnv) (expression : Expr) (rest : List Arg)
    (before after : RState) (roots : List (List RootRef))
    (checked : rpArgs environment (.byVal expression :: rest) before = .ok (roots, after)) :
    ∃ firstRoots firstAfter remainingRoots remainingAfter,
      rpExpr environment expression before = .ok (firstRoots, firstAfter) ∧
      rpArgs environment rest { firstAfter with eff := {} } = .ok (remainingRoots, remainingAfter) := by
  simp only [rpArgs, bind, StateT.bind] at checked
  unfold_argument_capture
  cases first : rpExpr environment expression before with
  | error failure => simp [first, Except.bind] at checked
  | ok result =>
    rcases result with ⟨firstRoots, firstAfter⟩
    simp only [first, Except.bind] at checked
    cases remaining : rpArgs environment rest { firstAfter with eff := {} } with
    | error failure =>
      rw [remaining] at checked
      change Except.error _ = Except.ok _ at checked
      cases checked
    | ok result => exact ⟨firstRoots, firstAfter, result.1, result.2, rfl, remaining⟩

#print axioms rpArgs_byValue_cons
end Goose.Proofs.ConstructionAcceptedExecution
