import Goose.Proofs.ConstructionAcceptedScalarAssignRoots
import Lean.Elab.Tactic

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def argumentRootsHelperName (name : String) : Lean.Name :=
  Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Roots") 0) "Goose") "Construct") name

elab "unfold_argument_capture" : tactic => do
  let capture := Lean.mkIdent (argumentRootsHelperName "captureEffects")
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $capture at *))

theorem rpArgs_twoByValue_operands (environment : PEnv) (left right : Expr) (before after : RState)
    (roots : List (List RootRef))
    (checked : rpArgs environment [.byVal left, .byVal right] before = .ok (roots, after)) :
    ∃ leftRoots leftAfter rightRoots rightAfter,
      rpExpr environment left before = .ok (leftRoots, leftAfter) ∧
      rpExpr environment right { leftAfter with eff := {} } = .ok (rightRoots, rightAfter) := by
  simp only [rpArgs, bind, StateT.bind] at checked
  unfold_argument_capture
  cases leftStep : rpExpr environment left before with
  | error failure => simp [leftStep, Except.bind] at checked
  | ok leftResult =>
    rcases leftResult with ⟨leftRoots, leftAfter⟩
    simp only [leftStep, Except.bind] at checked
    cases rightStep : rpExpr environment right { leftAfter with eff := {} } with
    | error failure => simp [rightStep, rpArgs, bind, StateT.bind, Except.bind] at checked
    | ok rightResult =>
      rcases rightResult with ⟨rightRoots, rightAfter⟩
      exact ⟨leftRoots, leftAfter, rightRoots, rightAfter, rfl, rightStep⟩

#print axioms rpArgs_twoByValue_operands
end Goose.Proofs.ConstructionAcceptedExecution
