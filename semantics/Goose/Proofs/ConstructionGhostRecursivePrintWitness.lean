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

private def nestedValue : Expr := .ifE (.bool true)
  (.mk 1 [.print [.text "branch"] 0] (some (.call 0 [] 0)))
  (.mk 2 [.abort "skipped" 0] (some (.lit .i64 3))) 0

private theorem nestedValueSyntax : ValueSyntax config nestedValue := by
  unfold nestedValue
  apply ValueSyntax.conditional
  · exact .base (.boolean true)
  · apply BlockValueSyntax.tail
    · intro statement member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst statement
      exact .printText "branch" 0
    · exact .call 0 [] 0 context implementation rfl rfl rfl .nil
  · apply BlockValueSyntax.tail
    · intro statement member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst statement
      exact .abort "skipped" 0
    · exact .base (.integer .i64 3)

theorem nestedValue_history (fuel : Nat) :
    SourceHistory config fuel [] (.value environment nestedValue) .initial (evalValue fuel config environment nestedValue .initial) :=
  fuelHistory_exists fuel config _ [] .initial ((syntaxFuel_existsWithTails fuel config closed).value environment nestedValue nestedValueSyntax)

theorem nestedValue_witness :
    SourceHistory config 40 [] (.value environment nestedValue) .initial (evalValue 40 config environment nestedValue .initial) ∧
    evalValue 40 config environment nestedValue .initial = .ok .unit (stepState (evalValue 40 config environment nestedValue .initial)) ∧
    (stepState (evalValue 40 config environment nestedValue .initial)).construction.stdout.data.toList = [98, 114, 97, 110, 99, 104, 10, 120, 10] := by
  refine ⟨nestedValue_history 40, ?_, ?_⟩ <;>
    simp only [stepState, config, context, implementation, environment, nestedValue] <;> cbv

private def blockValue : Expr := .blockE (.mk 1 [.expr (.call 0 [] 0) 0] (some (.lit .i64 7))) 0

private theorem blockValueSyntax : ValueSyntax config blockValue := by
  unfold blockValue
  apply ValueSyntax.blockValue
  apply ResultBlockSyntax.make
  · intro statement member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst statement
    exact .expression (.call 0 [] 0) 0 (.call 0 [] 0 context implementation rfl rfl rfl .nil)
  · exact .produced (.lit .i64 7) (.scalar (.integer .i64 7)) (.base (.integer .i64 7))
      (.scalar (.lit .i64 7) (.integer .i64 7) (.base (.integer .i64 7)))

theorem blockValue_history (fuel : Nat) :
    SourceHistory config fuel [] (.value environment blockValue) .initial (evalValue fuel config environment blockValue .initial) :=
  fuelHistory_exists fuel config _ [] .initial ((syntaxFuel_existsWithTails fuel config closed).value environment blockValue blockValueSyntax)

theorem blockValue_witness :
    SourceHistory config 40 [] (.value environment blockValue) .initial (evalValue 40 config environment blockValue .initial) ∧
    evalValue 40 config environment blockValue .initial = .ok (.int .i64 7) (stepState (evalValue 40 config environment blockValue .initial)) ∧
    (stepState (evalValue 40 config environment blockValue .initial)).construction.stdout.data.toList = [120, 10] := by
  refine ⟨blockValue_history 40, ?_, ?_⟩ <;>
    simp only [stepState, config, context, implementation, environment, blockValue] <;> cbv

#print axioms blockValue_history
#print axioms blockValue_witness
#print axioms nestedValue_history
#print axioms nestedValue_witness
#print axioms recursivePrint_history
#print axioms recursivePrint_witness
end Goose.Proofs.ConstructionGhostRecursivePrintWitness
