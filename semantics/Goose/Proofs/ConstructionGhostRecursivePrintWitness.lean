import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostRecursivePrintWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel

private def context : Context := ⟨0, "callee", [], [], []⟩
private def implementation : Impl := ⟨"callee", #[], #[], #[], .mk 0 [.print [.text "x"] 0] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def arguments : List PrintArg := [.text "a", .expr (.call 0 [] 0), .text "b"]
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem closed : ClosedModuleWithTails config := by
  intro contextId actualContext actualImplementation found implemented
  cases contextId with
  | zero =>
      have contextEq : actualContext = context := by simpa [config] using found.symm
      subst actualContext
      have implEq : actualImplementation = implementation := by simpa [config, context] using implemented.symm
      subst actualImplementation
      refine ⟨0, [.print [.text "x"] 0], none, rfl, ?_, .none⟩
      intro statement member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst statement
      exact .printText "x" 0
  | succ n => simp [config] at found

private theorem statementSyntax : StatementSyntax config (.print arguments 0) := by
  apply StatementSyntax.printArguments
  intro argument member
  simp only [arguments, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .text "a"
  · exact .expression (.call 0 [] 0) (.call 0 [] 0 context implementation rfl rfl rfl .nil)
  · exact .text "b"

theorem recursivePrint_history (fuel : Nat) :
    SourceHistory config fuel [] (.statement environment (.print arguments 0)) .initial
      (execStmt fuel config environment (.print arguments 0) .initial) :=
  fuelHistory_exists fuel config _ [] .initial ((syntaxFuel_existsWithTails fuel config closed).statement environment _ statementSyntax)

theorem recursivePrint_witness :
    SourceHistory config 40 [] (.statement environment (.print arguments 0)) .initial
      (execStmt 40 config environment (.print arguments 0) .initial) ∧
    execStmt 40 config environment (.print arguments 0) .initial = .ok (.normal .unit)
      (stepState (execStmt 40 config environment (.print arguments 0) .initial)) ∧
    (stepState (execStmt 40 config environment (.print arguments 0) .initial)).construction.stdout.data.toList = [120, 10, 97, 40, 41, 98, 10] := by
  refine ⟨recursivePrint_history 40, ?_, ?_⟩ <;>
    simp only [stepState, config, context, implementation, environment, arguments] <;> cbv

#print axioms recursivePrint_history
#print axioms recursivePrint_witness
end Goose.Proofs.ConstructionGhostRecursivePrintWitness
