import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostAssignmentWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel

private def context : Context := ⟨0, "callee", [], [], []⟩
private def implementation : Impl := ⟨"callee", #[], #[], #[], .mk 0 [.print [.text "rhs"] 0] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state
private def before : ExecutionState := stepState (bindRoot (.global 0) .unit .initial)
private def statement : Stmt := .assign (.global 0) (.call 0 [] 0) 0

private theorem closed : ClosedModuleWithTails config := by
  intro contextId actualContext actualImplementation found implemented
  cases contextId with
  | zero =>
      have contextEq : actualContext = context := by simpa [config] using found.symm
      subst actualContext
      have implEq : actualImplementation = implementation := by simpa [config, context] using implemented.symm
      subst actualImplementation
      refine ⟨0, [.print [.text "rhs"] 0], none, rfl, ?_, .none⟩
      intro actual member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst actual
      exact .printText "rhs" 0
  | succ n => simp [config] at found

private theorem statementSyntax : StatementSyntax config statement :=
  .assignment (.global 0) (.call 0 [] 0) 0 (.globalPlace 0) (.call 0 [] 0 context implementation rfl rfl rfl .nil)

theorem assignment_history (fuel : Nat) :
    SourceHistory config fuel [] (.statement environment statement) before (execStmt fuel config environment statement before) :=
  fuelHistory_exists fuel config _ [] before ((syntaxFuel_existsWithTails fuel config closed).statement environment statement statementSyntax)

theorem assignment_witness :
    SourceHistory config 40 [] (.statement environment statement) before (execStmt 40 config environment statement before) ∧
    execStmt 40 config environment statement before = .ok (.normal .unit) (stepState (execStmt 40 config environment statement before)) ∧
    (stepState (execStmt 40 config environment statement before)).construction.stdout.data.toList = [114, 104, 115, 10] := by
  refine ⟨assignment_history 40, ?_, ?_⟩ <;>
    simp only [stepState, before, config, context, implementation, environment, statement] <;> cbv

theorem terminalStatements_history (fuel : Nat) :
    SourceHistory config fuel [] (.statement environment (.exit (.lit .i64 7) 0)) before
      (execStmt fuel config environment (.exit (.lit .i64 7) 0) before) ∧
    SourceHistory config fuel [] (.statement environment (.abort "stop" 0)) before
      (execStmt fuel config environment (.abort "stop" 0) before) := by
  constructor
  · exact fuelHistory_exists fuel config _ [] before
      ((syntaxFuel_existsWithTails fuel config closed).statement environment _
        (.exit _ _ (.base (.integer .i64 7))))
  · exact fuelHistory_exists fuel config _ [] before
      ((syntaxFuel_existsWithTails fuel config closed).statement environment _ (.abort _ _))

theorem terminalStatements_witness :
    execStmt 40 config environment (.exit (.lit .i64 7) 0) before = .stop (.exit 7) before ∧
    execStmt 40 config environment (.abort "stop" 0) before = .stop (.abort .userAbort 0) before := by
  simp only [before, stepState, config, context, implementation, environment]
  constructor <;> cbv

#print axioms terminalStatements_history
#print axioms terminalStatements_witness
#print axioms assignment_history
#print axioms assignment_witness
end Goose.Proofs.ConstructionGhostAssignmentWitness
